require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8126036 [A B C D P] : Prf (∀ (λ << : El (fun A (fun A bool)), (∀ (λ p : El (fun (fun A B) (fun P bool)), (∀ (λ s : El (fun P A), (∀ (λ g : El (fun P (fun C D)), (∀ (λ y : El (fun (fun A B) (fun P C)), (⇒ ((@admissible A B A C P) << p s y) ((@admissible A B A D P) << p s (λ f : El (fun A B), (λ x : El P, (g x (y f x))))))))))))))));
