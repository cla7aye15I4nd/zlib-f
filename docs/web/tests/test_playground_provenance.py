"""The executable example must follow the selected upstream source and patches."""
from pathlib import Path
import hashlib
import json
import subprocess
import unittest

SITE=Path(__file__).resolve().parents[1]
REPO=SITE.parents[1]

class PlaygroundProvenanceTests(unittest.TestCase):
    def test_selected_source_and_patch_bytes(self):
        record=json.loads((SITE/'content/codec-playground-provenance.json').read_text())
        pin=subprocess.check_output(['git','ls-tree','HEAD','zlib'],cwd=REPO,text=True).split()[2]
        self.assertEqual(record['source_commit'],pin)
        patches=sorted((REPO/'patches').glob('*.patch'))
        self.assertEqual(record['source_patches'],[
            {'path':p.relative_to(REPO).as_posix(),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
            for p in patches
        ])
        self.assertEqual(record['target'],'wasm32-unknown-emscripten')
        self.assertEqual(record['configuration']['input_limit_bytes'],262144)

if __name__=='__main__':unittest.main()
