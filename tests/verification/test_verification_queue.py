"""Queue tests use tiny local repositories and never execute Lean checks."""
import importlib.util
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[2] / "scripts/verification-queue.py"
spec = importlib.util.spec_from_file_location("verification_queue", SCRIPT)
queue = importlib.util.module_from_spec(spec)
spec.loader.exec_module(queue)


class QueueTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.spool = self.root / "spool"
        self.run_git("init", "-q")
        (self.repo / "value").write_text("committed")
        self.run_git("add", "value")
        self.run_git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                     "commit", "-qm", "fixture")

    def run_git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.repo), *args], text=True).strip()

    def test_deduplicates_commit_and_stage_order(self):
        first, created = queue.enqueue(self.repo, self.spool, "HEAD", ["build", "audit"])
        second, repeated = queue.enqueue(self.repo, self.spool, "HEAD", ["audit", "build"])
        self.assertTrue(created)
        self.assertFalse(repeated)
        self.assertEqual(first, second)

    def test_concurrent_producers_publish_one_complete_request(self):
        with ThreadPoolExecutor(max_workers=8) as pool:
            results = list(pool.map(lambda _: queue.enqueue(self.repo, self.spool, "HEAD", ["build"]),
                                    range(8)))
        self.assertEqual(sum(created for _, created in results), 1)
        keys = {key for key, _ in results}
        self.assertEqual(len(keys), 1)
        job = self.spool / "jobs" / keys.pop()
        self.assertEqual(json.loads((job / "state.json").read_text())["status"], "queued")
        self.assertEqual(json.loads((job / "request.json").read_text())["commit"],
                         self.run_git("rev-parse", "HEAD"))

    def test_snapshot_excludes_uncommitted_changes(self):
        key, _ = queue.enqueue(self.repo, self.spool, "HEAD", ["build"])
        (self.repo / "value").write_text("dirty")
        with patch.dict(queue.STAGES, {"build": [sys.executable, "-c",
                "from pathlib import Path; assert Path('value').read_text() == 'committed'"]}):
            result = queue.process(self.spool / "jobs" / key, self.spool)
        self.assertEqual(result["status"], "passed")
        self.assertEqual((self.repo / "value").read_text(), "dirty")
        self.assertEqual(json.loads((self.spool / "events" / (key + ".json")).read_text())["commit"],
                         self.run_git("rev-parse", "HEAD"))

    def test_failure_stops_later_stages_and_emits_event(self):
        key, _ = queue.enqueue(self.repo, self.spool, "HEAD", ["build", "no-sorry"])
        with patch.dict(queue.STAGES, {"build": [sys.executable, "-c", "raise SystemExit(7)"]}):
            result = queue.process(self.spool / "jobs" / key, self.spool, "/missing-hook")
        self.assertEqual(result["status"], "failed")
        self.assertEqual(result["stages"][0]["exit"], 7)
        self.assertEqual(result["stages"][0]["name"], "build")
        self.assertEqual(len(result["stages"]), 1)
        self.assertTrue((self.spool / "jobs" / key / "notification.json").exists())
        self.assertTrue((self.spool / "events" / (key + ".json")).exists())

    def test_successful_hook_receives_durable_event(self):
        key, _ = queue.enqueue(self.repo, self.spool, "HEAD", ["build"])
        hook = self.root / "hook"
        received = self.root / "received"
        hook.write_text("#!" + sys.executable + "\nimport pathlib, sys\npathlib.Path(" +
                        repr(str(received)) + ").write_text(sys.argv[1])\n")
        hook.chmod(0o755)
        with patch.dict(queue.STAGES, {"build": [sys.executable, "-c", "pass"]}):
            queue.process(self.spool / "jobs" / key, self.spool, str(hook))
        event = Path(received.read_text())
        self.assertEqual(json.loads(event.read_text())["key"], key)
        self.assertEqual(json.loads((self.spool / "jobs" / key / "notification.json").read_text()),
                         {"exit": 0})

    def test_retry_preserves_previous_attempt(self):
        key, _ = queue.enqueue(self.repo, self.spool, "HEAD", ["build"])
        job = self.spool / "jobs" / key
        (job / "state.json").write_text('{"status":"running"}')
        (job / "build.log").write_text("old attempt")
        subprocess.run([sys.executable, str(SCRIPT), "--repository", str(self.repo),
                        "--spool", str(self.spool), "retry", key], check=True)
        self.assertEqual(json.loads((job / "state.json").read_text())["status"], "queued")
        self.assertEqual(next((job / "history").glob("*/build.log")).read_text(), "old attempt")


if __name__ == "__main__":
    unittest.main()
