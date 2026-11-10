"""Verify failure dispatch without starting a paid or remote session."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location('verification_agent',
    Path(__file__).resolve().parents[2] / 'scripts' / 'verification-agent.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class DiagnosisTests(unittest.TestCase):
    def test_failure_is_diagnosed_read_only_without_source_edits(self):
        with tempfile.TemporaryDirectory() as directory:
            job = Path(directory)
            (job / 'source').mkdir()
            event = job / 'event.json'
            event.write_text(json.dumps({'commit': 'a' * 40, 'status': 'failed',
                                         'result': str(job / 'state.json')}))
            with patch.object(MODULE.shutil, 'which', return_value='/bin/codex'), \
                 patch.object(MODULE.subprocess, 'run') as run:
                run.return_value.returncode = 0
                self.assertEqual(MODULE.diagnose(event), 0)
                command = run.call_args.args[0]
                self.assertEqual(command[command.index('--sandbox') + 1], 'read-only')
                self.assertIn('Do not write proofs', run.call_args.kwargs['input'])
                self.assertEqual(json.loads((job / 'agent-result.json').read_text())['exit'], 0)

    def test_success_does_not_start_agent(self):
        with tempfile.TemporaryDirectory() as directory:
            event = Path(directory) / 'event.json'
            event.write_text(json.dumps({'status': 'passed'}))
            with patch.object(MODULE.sys, 'argv', ['hook', str(event)]), \
                 patch.object(MODULE.subprocess, 'Popen') as start:
                self.assertEqual(MODULE.main(), 0)
                start.assert_not_called()


if __name__ == '__main__':
    unittest.main()
