require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8101084 [A B P] : Prf (∀ (λ << : El (fun A (fun A bool)), (∀ (λ p : El (fun (fun A B) (fun P bool)), (∀ (λ s : El (fun P A), (∀ (λ t : El (fun P A), (⇒ (∀ (λ f : El (fun A B), (∀ (λ a : El P, (⇒ (p f a) (<< (t a) (s a))))))) ((@admissible A B A B P) << p s (λ f : El (fun A B), (λ x : El P, (f (t x))))))))))))));
