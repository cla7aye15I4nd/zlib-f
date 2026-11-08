"""Build the independent reading site and its complete reference."""
from pathlib import Path
import shutil
from reference import build_reference
from reading import build_reading

ROOT=Path(__file__).resolve().parent
OUT=ROOT/'dist'
if OUT.exists():
    shutil.rmtree(OUT)
OUT.mkdir()
shutil.copytree(ROOT/'static',OUT/'static')
(OUT/'.nojekyll').touch()
build_reference()
build_reading()
