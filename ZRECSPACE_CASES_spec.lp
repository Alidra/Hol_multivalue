require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1058927 [A] : Prf (∀ (λ a : El (fun num (fun A bool)), (= ((@ZRECSPACE A) a) (∨ (= a (@ZBOT A)) (∃ (λ c : El num, (∃ (λ i : El A, (∃ (λ r : El (fun num (fun num (fun A bool))), (∧ (= a ((@ZCONSTR A) c i r)) (∀ (λ n : El num, ((@ZRECSPACE A) (r n)))))))))))))));
