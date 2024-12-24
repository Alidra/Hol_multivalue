require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1058928 [A] : Prf (∀ (λ ZRECSPACE' : El (fun (fun num (fun A bool)) bool), (⇒ (∧ (ZRECSPACE' (@ZBOT A)) (∀ (λ c : El num, (∀ (λ i : El A, (∀ (λ r : El (fun num (fun num (fun A bool))), (⇒ (∀ (λ n : El num, (ZRECSPACE' (r n)))) (ZRECSPACE' ((@ZCONSTR A) c i r)))))))))) (∀ (λ a : El (fun num (fun A bool)), (⇒ ((@ZRECSPACE A) a) (ZRECSPACE' a)))))));
