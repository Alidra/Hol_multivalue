require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1052523 : Prf ((λ Y : El (fun (prod num (prod num (prod num (prod num (prod num num))))) (fun num num)), (∀ (λ _17341 : El (prod num (prod num (prod num (prod num (prod num num))))), (∀ (λ x : El num, (∀ (λ y : El num, (∧ (= (NUMFST (NUMPAIR x y)) x) (= (Y _17341 (NUMPAIR x y)) y))))))))) ((@ε (fun (prod num (prod num (prod num (prod num (prod num num))))) (fun num num))) (λ Y : El (fun (prod num (prod num (prod num (prod num (prod num num))))) (fun num num)), (∀ (λ _17341 : El (prod num (prod num (prod num (prod num (prod num num))))), (∀ (λ x : El num, (∀ (λ y : El num, (∧ (= (NUMFST (NUMPAIR x y)) x) (= (Y _17341 (NUMPAIR x y)) y)))))))))));
