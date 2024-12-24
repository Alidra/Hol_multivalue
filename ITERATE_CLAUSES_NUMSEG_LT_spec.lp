require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6194987 [_123501] (f : El (fun num _123501)) : Prf (∀ (λ op : El (fun _123501 (fun _123501 _123501)), (⇒ ((@monoidal _123501) op) (∧ (= ((@iterate _123501 num) op ((@GSPEC num) (λ GEN_PVAR_254 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_254 (< i (NUMERAL _0)) i))))) f) ((@neutral _123501) op)) (∀ (λ k : El num, (= ((@iterate _123501 num) op ((@GSPEC num) (λ GEN_PVAR_255 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_255 (< i (SUC k)) i))))) f) (op ((@iterate _123501 num) op ((@GSPEC num) (λ GEN_PVAR_256 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_256 (< i k) i))))) f) (f k)))))))));
