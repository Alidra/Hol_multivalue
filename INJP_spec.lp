require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1056993 [A] : Prf (∀ (λ f1 : El (fun num (fun A bool)), (∀ (λ f2 : El (fun num (fun A bool)), (= ((@INJP A) f1 f2) (λ n : El num, (λ a : El A, ((@COND bool) (NUMLEFT n) (f1 (NUMRIGHT n) a) (f2 (NUMRIGHT n) a)))))))));
