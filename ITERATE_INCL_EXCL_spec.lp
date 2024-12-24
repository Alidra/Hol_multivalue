require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5778669 [_120960 _120978] : Prf (∀ (λ op : El (fun _120978 (fun _120978 _120978)), (⇒ ((@monoidal _120978) op) (∀ (λ s : El (fun _120960 bool), (∀ (λ t : El (fun _120960 bool), (∀ (λ f : El (fun _120960 _120978), (⇒ (∧ ((@FINITE _120960) s) ((@FINITE _120960) t)) (= (op ((@iterate _120978 _120960) op s f) ((@iterate _120978 _120960) op t f)) (op ((@iterate _120978 _120960) op ((@UNION _120960) s t) f) ((@iterate _120978 _120960) op ((@INTER _120960) s t) f)))))))))))));
