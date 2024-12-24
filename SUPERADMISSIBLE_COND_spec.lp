require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8291440 [A B P] : Prf (∀ (λ << : El (fun A (fun A bool)), (∀ (λ p : El (fun (fun A B) (fun P bool)), (∀ (λ P' : El (fun (fun A B) (fun P bool)), (∀ (λ s : El (fun P A), (∀ (λ h : El (fun (fun A B) (fun P B)), (∀ (λ k : El (fun (fun A B) (fun P B)), (⇒ (∧ ((@admissible A B A bool P) << p s P') (∧ ((@superadmissible A B P) << (λ f : El (fun A B), (λ x : El P, (∧ (p f x) (P' f x)))) s h) ((@superadmissible A B P) << (λ f : El (fun A B), (λ x : El P, (∧ (p f x) (¬ (P' f x))))) s k))) ((@superadmissible A B P) << p s (λ f : El (fun A B), (λ x : El P, ((@COND B) (P' f x) (h f x) (k f x))))))))))))))))));
