Require Import Bootstrap.

Extraction Language Haskell.

Extract Inductive option => 
  "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive bool => 
  "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive prod => "(,)" ["(,)"].

Extraction Inline and_rect sig_rect proj1_sig LEQ.
Extraction Inline pLEQ aLEQ meldUniq_terminate.
Extraction Inline 
  preInsert preFindMin preMeld 
  preExtractMin preEmpty preToList.

Extraction "BootExtract.hs" 
  bootPQ empty insert 
  findMin extractMin toList meld.
