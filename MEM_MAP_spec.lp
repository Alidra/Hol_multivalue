require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1147568 [_26978 _26981] : Prf (∀ (λ f : El (fun _26981 _26978), (∀ (λ y : El _26978, (∀ (λ l : El (list _26981), (= ((@MEM _26978) y ((@MAP _26981 _26978) f l)) (∃ (λ x : El _26981, (∧ ((@MEM _26981) x l) (= y (f x))))))))))));
