require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1057928 [A] : Prf (∀ (λ c : El num, (∀ (λ i : El A, (∀ (λ r : El (fun num (fun num (fun A bool))), (= ((@ZCONSTR A) c i r) ((@INJP A) ((@INJN A) (SUC c)) ((@INJP A) ((@INJA A) i) ((@INJF A) r))))))))));
