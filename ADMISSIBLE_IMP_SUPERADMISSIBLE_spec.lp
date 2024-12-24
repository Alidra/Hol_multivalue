require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8239494 [A B P] : Prf (∀ (λ << : El (fun A (fun A bool)), (∀ (λ p : El (fun (fun A B) (fun P bool)), (∀ (λ s : El (fun P A), (∀ (λ t : El (fun (fun A B) (fun P B)), (⇒ ((@admissible A B A B P) << p s t) ((@superadmissible A B P) << p s t))))))))));
