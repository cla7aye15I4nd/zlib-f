#!/usr/bin/env python3
"""Routing/fail-closed tests only. No fixture is an approved lock or proof run."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

FILES=Path(__file__).resolve().parents[2]
PROJECT=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=FILES,text=True).strip())
sys.path.insert(0,str(PROJECT/'scripts'))
spec=importlib.util.spec_from_file_location('scoped_wiring_verification',FILES/'scripts/verification.py')
v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v);v.ROOT=PROJECT
SHA='a'*40

class Routing(unittest.TestCase):
    def invoke(self,mode,shard=0,failure=False):
        policy=json.loads((PROJECT/'tests/audit/policy.lock').read_text())
        argv=['verification.py',mode,'--baseline',SHA,'--scoped-approved-commit',SHA]
        if mode=='mutants':argv+=['--shard-count','4','--shard-index',str(shard)]
        with contextlib.ExitStack() as stack:
            stack.enter_context(patch.object(sys,'argv',argv))
            for name,value in [('coverage',{}),('source_policy',policy),('audit',0)]:
                stack.enter_context(patch.object(v,name,return_value=value))
            for name in ['check_baseline','check_versioned_sources','build_library','mutation_partition',
                         'check_public_mutant_spans','check_public_mutant_coverage','check_locks']:
                stack.enter_context(patch.object(v,name))
            public=stack.enter_context(patch.object(v,'run_public_mutants'))
            replay=stack.enter_context(patch.object(v,'replay_public_mutants'))
            scoped=stack.enter_context(patch.object(v,'run_scoped_default_admission',
                side_effect=subprocess.CalledProcessError(1,['scoped-child']) if failure else None))
            commands=stack.enter_context(patch.object(v,'run'))
            stack.enter_context(patch.object(v.subprocess,'check_output',return_value=''))
            stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
            stack.enter_context(contextlib.redirect_stderr(io.StringIO()))
            result=v.main()
            return result,public.call_count,replay.call_count,scoped.call_count,commands.call_args_list

    def test_each_shard_keeps_public_scoped_exactly_once(self):
        results=[self.invoke('mutants',i) for i in range(4)]
        self.assertEqual([r[0] for r in results],[0,0,0,0])
        self.assertEqual([r[1] for r in results],[1,1,1,1])
        self.assertEqual([r[3] for r in results],[1,0,0,0])

    def test_final_keeps_public_replay_scoped_once(self):
        rc,_,replay,scoped,_=self.invoke('final')
        self.assertEqual((rc,replay,scoped),(0,1,1))

    def test_child_failure_returns_one_and_stops_following_tests(self):
        for mode in ['mutants','final']:
            rc,_,_,count,commands=self.invoke(mode,failure=True)
            self.assertEqual((rc,count),(1,1))
            self.assertFalse(any('tests/run.sh' in str(call) for call in commands))

    def test_missing_or_mutable_approval_fails_without_child(self):
        for approval in [None,'HEAD','origin/main','a'*39]:
            with self.subTest(approval=approval),patch.object(v.subprocess,'run') as child:
                with self.assertRaises(v.Rejected):v.run_scoped_default_admission(approval,SHA)
                child.assert_not_called()
        with patch.object(v.subprocess,'run') as child:
            with self.assertRaises(v.Rejected):v.run_scoped_default_admission(SHA,None)
            child.assert_not_called()

    def test_approved_tool_path_and_checked_exit(self):
        # A process-routing mock, not lock/approval or semantic validation.
        with patch.object(v.subprocess,'check_output',return_value=SHA+'\n'),patch.object(v.subprocess,'run') as child:
            v.run_scoped_default_admission(SHA,SHA)
            args=child.call_args.args[0]
            self.assertEqual(args[1],str(v.AUDITOR_ROOT/'tests/proofmut/deflate-default-scoped-null-output.py'))
            self.assertTrue(child.call_args.kwargs['check'])

    def test_workflow_authority(self):
        final=(FILES/'.github/workflows/verification-final.yml').read_text()
        normal=(FILES/'.github/workflows/lean.yml').read_text()
        self.assertIn('baseline=$(git rev-parse origin/main)',final)
        self.assertNotIn('inputs.approved',final)
        self.assertIn('--scoped-approved-commit "$baseline"',final)
        self.assertIn('vars.ZLIBF_SCOPED_ADMISSION_APPROVED_COMMIT',normal)
        self.assertIn('git worktree add --detach "$approved" "$APPROVED_ADMISSION_COMMIT"',normal)

if __name__=='__main__':unittest.main()
