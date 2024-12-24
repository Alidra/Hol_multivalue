require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3648775 [_93408 _93424] : Prf (∀ (λ P : El (fun (fun _93424 bool) bool), (∀ (λ f : El (fun _93408 _93424), (∀ (λ s : El (fun _93408 bool), (= (∀ (λ t : El (fun _93424 bool), (⇒ ((@SUBSET _93424) t ((@IMAGE _93408 _93424) f s)) (P t)))) (∀ (λ t : El (fun _93408 bool), (⇒ ((@SUBSET _93408) t s) (P ((@IMAGE _93408 _93424) f t))))))))))));
