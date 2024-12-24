require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem361737 [A B] : Prf (∀ (λ << : El (fun B (fun B bool)), (∀ (λ m : El (fun A B), (⇒ ((@WF B) <<) ((@WF A) (λ x : El A, (λ x' : El A, (<< (m x) (m x'))))))))));
