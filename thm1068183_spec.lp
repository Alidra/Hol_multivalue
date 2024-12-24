require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1068183 [A B] : Prf ((λ OUTL' : El (fun (prod num (prod num (prod num num))) (fun (Sum A B) A)), (∀ (λ _17486 : El (prod num (prod num (prod num num))), (∀ (λ x : El A, (= (OUTL' _17486 ((@INL A B) x)) x)))))) ((@ε (fun (prod num (prod num (prod num num))) (fun (Sum A B) A))) (λ OUTL' : El (fun (prod num (prod num (prod num num))) (fun (Sum A B) A)), (∀ (λ _17486 : El (prod num (prod num (prod num num))), (∀ (λ x : El A, (= (OUTL' _17486 ((@INL A B) x)) x))))))));
