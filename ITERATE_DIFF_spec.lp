require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5772504 [_120745 _120749] : Prf (∀ (λ op : El (fun _120749 (fun _120749 _120749)), (⇒ ((@monoidal _120749) op) (∀ (λ f : El (fun _120745 _120749), (∀ (λ s : El (fun _120745 bool), (∀ (λ t : El (fun _120745 bool), (⇒ (∧ ((@FINITE _120745) s) ((@SUBSET _120745) t s)) (= (op ((@iterate _120749 _120745) op ((@DIFF _120745) s t) f) ((@iterate _120749 _120745) op t f)) ((@iterate _120749 _120745) op s f))))))))))));
