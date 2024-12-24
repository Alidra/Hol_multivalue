require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7070368 [A] : Prf (∀ (λ f : El (fun A real), (∀ (λ c : El real, (∀ (λ s : El (fun A bool), (= ((@sum A) s (λ x : El A, (real_mul (f x) c))) (real_mul ((@sum A) s f) c))))))));
