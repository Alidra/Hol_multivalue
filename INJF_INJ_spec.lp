require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1056666 [A] : Prf (∀ (λ f1 : El (fun num (fun num (fun A bool))), (∀ (λ f2 : El (fun num (fun num (fun A bool))), (= (= ((@INJF A) f1) ((@INJF A) f2)) (= f1 f2))))));
