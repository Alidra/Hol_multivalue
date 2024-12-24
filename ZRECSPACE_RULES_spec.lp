require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1058926 [A] : Prf (∧ ((@ZRECSPACE A) (@ZBOT A)) (∀ (λ c : El num, (∀ (λ i : El A, (∀ (λ r : El (fun num (fun num (fun A bool))), (⇒ (∀ (λ n : El num, ((@ZRECSPACE A) (r n)))) ((@ZRECSPACE A) ((@ZCONSTR A) c i r))))))))));
