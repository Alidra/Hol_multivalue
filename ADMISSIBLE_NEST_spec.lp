require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8133916 [A B P] : Prf (∀ (λ << : El (fun A (fun A bool)), (∀ (λ p : El (fun (fun A B) (fun P bool)), (∀ (λ s : El (fun P A), (∀ (λ t : El (fun (fun A B) (fun P A)), (⇒ (∧ ((@admissible A B A A P) << p s t) (∀ (λ f : El (fun A B), (∀ (λ a : El P, (⇒ (p f a) (<< (t f a) (s a)))))))) ((@admissible A B A B P) << p s (λ f : El (fun A B), (λ x : El P, (f (t f x))))))))))))));
