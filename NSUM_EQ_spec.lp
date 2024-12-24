require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6938831 [_127166] : Prf (∀ (λ f : El (fun _127166 num), (∀ (λ g : El (fun _127166 num), (∀ (λ s : El (fun _127166 bool), (⇒ (∀ (λ x : El _127166, (⇒ ((@IN _127166) x s) (= (f x) (g x))))) (= ((@nsum _127166) s f) ((@nsum _127166) s g)))))))));
