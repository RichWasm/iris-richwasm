import initWabt from "wabt";

initWabt().then((wabt) => {
  self.wabt = wabt;
  importScripts("./compiler_worker.bc.js");
});
