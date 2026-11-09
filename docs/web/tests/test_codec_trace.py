"""Guard the provenance and fixed input of the displayed C measurements."""
from pathlib import Path
import hashlib
import json
import subprocess
import unittest

SITE=Path(__file__).resolve().parents[1]
DATA=json.loads((SITE/'content/codec-trace.json').read_text())

class CodecTraceTests(unittest.TestCase):
    def test_record_uses_the_selected_source_and_registered_patches(self):
        pin=subprocess.check_output(['git','ls-tree','HEAD','zlib'],cwd=SITE.parents[1],text=True).split()[2]
        self.assertEqual(DATA['source_commit'],pin)
        self.assertEqual(DATA['source_patches'],sorted(p.name for p in (SITE.parents[1]/'patches').glob('*.patch')))
        self.assertEqual(DATA['kind'],'fixed-source-native-example-runs')
        self.assertTrue(DATA['measurement']['first_block_only'])
        self.assertIsNone(DATA['measurement']['internal_function_counts'])

    def test_input_identity_is_independently_reproducible(self):
        region=65536
        text=b'kind=reading;value=01234567;pattern=ABABABAB;state=ready;\n'
        data=bytearray(3*region)
        for i in range(region):
            marker=i%97
            data[i]=48+((i//97)>>(3*marker))%10 if marker<8 else text[i%len(text)]
            data[region+i]=65+(i//1024)%4
        state=0x12345678
        for i in range(region):
            state^=(state<<13)&0xffffffff
            state^=state>>17
            state^=(state<<5)&0xffffffff
            data[2*region+i]=state&255
        self.assertEqual(len(data),DATA['input']['bytes'])
        self.assertEqual(hashlib.sha256(data).hexdigest(),DATA['input']['sha256'])

    def test_all_configuration_records_roundtrip_the_same_input(self):
        cases=DATA['cases'];self.assertEqual(len({c['name'] for c in cases}),16)
        self.assertEqual({c['wrapper'] for c in cases},{'raw','zlib','gzip'})
        self.assertEqual({c['deflate_init']['strategy'] for c in cases},{0,1,2,3,4})
        for c in cases:
            self.assertTrue(c['roundtrip'],c['name'])
            self.assertEqual(c['decoded_bytes'],DATA['input']['bytes'])
            self.assertGreater(c['compressed_bytes'],0)
            self.assertGreater(c['deflate_calls'],0)
            self.assertGreater(c['inflate_calls'],0)
            self.assertEqual(c['first_block']['type_bits'],{'stored':0,'fixed':1,'dynamic':2}[c['first_block']['type']])
            self.assertEqual(c['payload_offset'],{'raw':0,'zlib':2,'gzip':10}[c['wrapper']])

if __name__=='__main__':unittest.main()
