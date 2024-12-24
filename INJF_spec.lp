require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1056444 [A] : Prf (∀ (λ f : El (fun num (fun num (fun A bool))), (= ((@INJF A) f) (λ n : El num, (f (NUMFST n) (NUMSND n))))));
