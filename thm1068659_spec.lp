require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1068659 [A B] : Prf ((λ OUTR' : El (fun (prod num (prod num (prod num num))) (fun (Sum A B) B)), (∀ (λ _17488 : El (prod num (prod num (prod num num))), (∀ (λ y : El B, (= (OUTR' _17488 ((@INR A B) y)) y)))))) ((@ε (fun (prod num (prod num (prod num num))) (fun (Sum A B) B))) (λ OUTR' : El (fun (prod num (prod num (prod num num))) (fun (Sum A B) B)), (∀ (λ _17488 : El (prod num (prod num (prod num num))), (∀ (λ y : El B, (= (OUTR' _17488 ((@INR A B) y)) y))))))));
