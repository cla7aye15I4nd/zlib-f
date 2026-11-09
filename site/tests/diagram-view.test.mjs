import test from 'node:test';
import assert from 'node:assert/strict';
import {diagramBox,diagramScale} from '../static/diagram-view.mjs';

const svg=attrs=>({getAttribute:name=>attrs[name]??null});

test('wide call graphs retain their natural drawing area',()=>{
  assert.deepEqual(diagramBox(svg({viewBox:'-8 -8 2410.4 900.1',width:'100%'})),{width:2411,height:901});
  assert.deepEqual(diagramBox(svg({viewBox:'0,0,450,120'})),{width:450,height:120});
  assert.deepEqual(diagramBox(svg({width:'850px',height:'500px'})),{width:850,height:500});
});

test('missing or invalid geometry cannot silently collapse a graph',()=>{
  for(const attrs of [{},{viewBox:'0 0 NaN 500'},{viewBox:'0 0 -1 20'},{width:'100%',height:'0'}])
    assert.throws(()=>diagramBox(svg(attrs)));
});

test('zoom keeps a readable floor instead of squeezing wide graphs into a phone',()=>{
  assert.equal(diagramScale(1),1);
  assert.equal(diagramScale(390/2411),.8);
  assert.equal(diagramScale(100),2.5);
  assert.equal(diagramScale(NaN),1);
});
