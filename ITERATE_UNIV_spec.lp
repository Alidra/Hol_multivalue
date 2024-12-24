require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6963073 [_127673 _127692] : Prf (∀ (λ op : El (fun _127673 (fun _127673 _127673)), (⇒ ((@monoidal _127673) op) (∀ (λ f : El (fun _127692 _127673), (∀ (λ s : El (fun _127692 bool), (⇒ ((@SUBSET _127692) ((@support _127692 _127673) op f (@UNIV _127692)) s) (= ((@iterate _127673 _127692) op s f) ((@iterate _127673 _127692) op (@UNIV _127692) f))))))))));
