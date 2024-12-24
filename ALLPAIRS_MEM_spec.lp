require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1181594 [_27494 _27495] : Prf (∀ (λ P : El (fun _27495 (fun _27494 bool)), (∀ (λ l : El (list _27495), (∀ (λ m : El (list _27494), (= (∀ (λ x : El _27495, (∀ (λ y : El _27494, (⇒ (∧ ((@MEM _27495) x l) ((@MEM _27494) y m)) (P x y)))))) ((@ALLPAIRS _27494 _27495) P l m))))))));
