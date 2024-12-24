require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8004099 [_141895 _141896 _141897] (s : El (fun (cart _141895 _141896) bool)) (t : El (fun (cart _141895 _141897) bool)) (P : El (fun (cart _141895 (finite_sum _141896 _141897)) bool)) : Prf (= T (= (∃ (λ z : El (cart _141895 (finite_sum _141896 _141897)), (∧ ((@IN (cart _141895 (finite_sum _141896 _141897))) z ((@PCROSS _141895 _141896 _141897) s t)) (P z)))) (∃ (λ x : El (cart _141895 _141896), (∃ (λ y : El (cart _141895 _141897), (∧ ((@IN (cart _141895 _141896)) x s) (∧ ((@IN (cart _141895 _141897)) y t) (P ((@pastecart _141895 _141896 _141897) x y))))))))));
