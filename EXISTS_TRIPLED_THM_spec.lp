require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem56911 [_5851 _5852 _5853] : Prf (∀ (λ P : El (fun _5853 (fun _5852 (fun _5851 bool))), (= (∃ ((@GABS (fun (prod _5853 (prod _5852 _5851)) bool)) (λ f : El (fun (prod _5853 (prod _5852 _5851)) bool), (∀ (λ x : El _5853, (∀ (λ y : El _5852, (∀ (λ z : El _5851, ((@GEQ bool) (f ((@̦‚ _5853 (prod _5852 _5851)) x ((@̦‚ _5852 _5851) y z))) (P x y z))))))))))) (∃ (λ x : El _5853, (∃ (λ y : El _5852, (∃ (λ z : El _5851, (P x y z))))))))));
