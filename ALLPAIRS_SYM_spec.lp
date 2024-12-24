require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1177679 [_27459 _27460] : Prf (∀ (λ P : El (fun _27460 (fun _27459 bool)), (∀ (λ l : El (list _27460), (∀ (λ m : El (list _27459), (= ((@ALLPAIRS _27459 _27460) P l m) ((@ALLPAIRS _27460 _27459) (λ x : El _27459, (λ y : El _27460, (P y x))) m l))))))));
