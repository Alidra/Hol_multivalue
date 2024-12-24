require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1065430 [A B] : Prf (∀ (λ Fn : El (fun num (fun A (fun (fun num (recspace A)) (fun (fun num B) B)))), (∃ (λ f : El (fun (recspace A) B), (∀ (λ c : El num, (∀ (λ i : El A, (∀ (λ r : El (fun num (recspace A)), (= (f ((@CONSTR A) c i r)) (Fn c i r (λ n : El num, (f (r n)))))))))))))));
