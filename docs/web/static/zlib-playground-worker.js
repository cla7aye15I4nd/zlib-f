import createCodecModule from './vendor/zlib-playground.js';
import {PLAYGROUND_LIMIT,readPlaygroundRecords} from './zlib-playground-model.mjs';

let loading;
self.onmessage=async event=>{
  const {id,bytes}=event.data||{};
  if(!(bytes instanceof ArrayBuffer)||bytes.byteLength>PLAYGROUND_LIMIT){self.postMessage({type:'error',id,code:'input'});return;}
  self.postMessage({type:'loading',id});
  let module,input=0;
  try{
    loading??=createCodecModule();module=await loading;
    const source=new Uint8Array(bytes);
    input=module._malloc(Math.max(1,source.length));
    if(!input)throw new Error('allocation');
    module.HEAPU8.set(source,input);
    const result=module._codec_run(input,source.length);
    const records=readPlaygroundRecords(module.HEAPU8,module._codec_records(),module._codec_record_count());
    const packed=module.HEAPU8.slice(module._codec_packed(),module._codec_packed()+module._codec_packed_length());
    const restored=module.HEAPU8.slice(module._codec_restored(),module._codec_restored()+module._codec_restored_length());
    const equal=module._codec_equal()===1,errorCode=module._codec_error(),streamSize=module._codec_stream_size();
    module._codec_reset();module._free(input);input=0;
    self.postMessage({type:result===0?'result':'error',id,code:result===0?null:'codec',errorCode,records,equal,inputLength:source.length,packed:packed.buffer,restored:restored.buffer,runtime:{abi:'wasm32',streamSize},released:true},[packed.buffer,restored.buffer]);
  }catch(error){
    self.postMessage({type:'error',id,code:error.message==='allocation'?'allocation':'runtime'});
  }finally{
    if(module){module._codec_reset();if(input)module._free(input);}
  }
};
