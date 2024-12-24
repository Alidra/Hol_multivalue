require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1057571 [A] : Prf (∀ (λ f1 : El (fun num (fun A bool)), (∀ (λ f1' : El (fun num (fun A bool)), (∀ (λ f2 : El (fun num (fun A bool)), (∀ (λ f2' : El (fun num (fun A bool)), (= (= ((@INJP A) f1 f2) ((@INJP A) f1' f2')) (∧ (= f1 f1') (= f2 f2')))))))))));
