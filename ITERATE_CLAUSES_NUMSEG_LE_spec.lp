require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6198343 [_123593] (f : El (fun num _123593)) : Prf (∀ (λ op : El (fun _123593 (fun _123593 _123593)), (⇒ ((@monoidal _123593) op) (∧ (= ((@iterate _123593 num) op ((@GSPEC num) (λ GEN_PVAR_257 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_257 (<= i (NUMERAL _0)) i))))) f) (f (NUMERAL _0))) (∀ (λ k : El num, (= ((@iterate _123593 num) op ((@GSPEC num) (λ GEN_PVAR_258 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_258 (<= i (SUC k)) i))))) f) (op ((@iterate _123593 num) op ((@GSPEC num) (λ GEN_PVAR_259 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_259 (<= i k) i))))) f) (f (SUC k))))))))));
