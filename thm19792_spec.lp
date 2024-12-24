require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem19792 [_3571 _3575] (s : El (fun _3575 _3571)) (t : El (fun _3575 _3571)) : Prf (= T (= (= s (λ x : El _3575, (t x))) (∀ (λ x : El _3575, (= (s x) (t x))))));
