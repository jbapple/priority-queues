Require Import Bootstrap.

Extraction Language Haskell.

Extract Inductive option => 
  "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive bool => 
  "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive list => "[]" ["[]" "(:)"].
Extract Inductive comparison => 
  "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].

Extraction Inline and_rect sig_rect proj1_sig LEQ.
Extraction Inline pLEQ aLEQ meld1.
Extraction Inline 
  preInsert preFindMin preMeld 
  preExtractMin preEmpty preToList.

Extraction "BootExtract.hs" 
  bootPQ empty insert 
  findMin extractMin toList meld.
