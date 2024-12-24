require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1060638 [A] : Prf (∀ (λ c1 : El num, (∀ (λ i1 : El A, (∀ (λ r1 : El (fun num (recspace A)), (∀ (λ c2 : El num, (∀ (λ i2 : El A, (∀ (λ r2 : El (fun num (recspace A)), (= (= ((@CONSTR A) c1 i1 r1) ((@CONSTR A) c2 i2 r2)) (∧ (= c1 c2) (∧ (= i1 i2) (= r1 r2))))))))))))))));
