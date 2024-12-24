require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4389660 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A B), (= (= ((@RESTRICTION A B) s f) f) ((@IN (fun A B)) f ((@EXTENSIONAL A B) s)))))));
