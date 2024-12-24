Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_UNIONS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm18394_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3343019 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3343020 {_87075 : Type'} (s : type686 _87075) (t : type686 _87075) : (@SUBSET (_87075 -> Prop) s t) = (term1 _87075 s t).
Proof. exact (@lem3343019 (_87075 -> Prop) s t). Qed.
Lemma lem3343021 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (@SUBSET (_87075 -> Prop) f g) = (term1 _87075 f g).
Proof. exact (@lem3343020 _87075 f g). Qed.
Lemma lem3343028 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3343029 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term2 _87075 f g) = (term3 _87075 f g).
Proof. exact (MK_COMB (@lem3343028) (@lem3343021 _87075 f g)). Qed.
Lemma lem3343031 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3343032 {_87075 : Type'} (s : _87075 -> Prop) (t : _87075 -> Prop) : (@SUBSET _87075 s t) = (term0 _87075 s t).
Proof. exact (@lem3343031 _87075 s t). Qed.
Lemma lem3343033 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term4 _87075 f g) = (term5 _87075 f g).
Proof. exact (@lem3343032 _87075 (@UNIONS _87075 f) (@UNIONS _87075 g)). Qed.
Lemma lem3343040 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term6 _87075 f g) = (term7 _87075 f g).
Proof. exact (MK_COMB (@lem3343029 _87075 f g) (@lem3343033 _87075 f g)). Qed.
Lemma lem3343043 {_87075 : Type'} (f : type686 _87075) : (term8 _87075 f) = (term9 _87075 f).
Proof. exact (fun_ext (fun g : type686 _87075 => @lem3343040 _87075 f g)). Qed.
Lemma lem3343044 {_87075 : Type'} : (@all ((_87075 -> Prop) -> Prop)) = (@all ((_87075 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87075 -> Prop) -> Prop))). Qed.
Lemma lem3343045 {_87075 : Type'} (f : type686 _87075) : (term10 _87075 f) = (term11 _87075 f).
Proof. exact (MK_COMB (@lem3343044 _87075) (@lem3343043 _87075 f)). Qed.
Lemma lem3343050 {_87075 : Type'} : (term12 _87075) = (term13 _87075).
Proof. exact (fun_ext (fun f : type686 _87075 => @lem3343045 _87075 f)). Qed.
Lemma lem3343051 {_87075 : Type'} : (@all ((_87075 -> Prop) -> Prop)) = (@all ((_87075 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87075 -> Prop) -> Prop))). Qed.
Lemma lem3343052 {_87075 : Type'} : (term14 _87075) = (term15 _87075).
Proof. exact (MK_COMB (@lem3343051 _87075) (@lem3343050 _87075)). Qed.
Lemma lem3343057 {_87075 : Type'} : (term15 _87075) = (term14 _87075).
Proof. exact (SYM (@lem3343052 _87075)). Qed.
Lemma lem3343075 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3343076 {_87075 : Type'} (P : type686 _87075) (x : _87075 -> Prop) : (@IN (_87075 -> Prop) x P) = (P x).
Proof. exact (@lem3343075 (_87075 -> Prop) P x). Qed.
Lemma lem3343077 {_87075 : Type'} (f : type686 _87075) (x : _87075 -> Prop) : (@IN (_87075 -> Prop) x f) = (f x).
Proof. exact (@lem3343076 _87075 f x). Qed.
Lemma lem3343078 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3343079 {_87075 : Type'} (f : type686 _87075) (x : _87075 -> Prop) : (term16 _87075 x f) = (term17 _87075 f x).
Proof. exact (MK_COMB (@lem3343078) (@lem3343077 _87075 f x)). Qed.
Lemma lem3343081 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3343082 {_87075 : Type'} (P : type686 _87075) (x : _87075 -> Prop) : (@IN (_87075 -> Prop) x P) = (P x).
Proof. exact (@lem3343081 (_87075 -> Prop) P x). Qed.
Lemma lem3343083 {_87075 : Type'} (g : type686 _87075) (x : _87075 -> Prop) : (@IN (_87075 -> Prop) x g) = (g x).
Proof. exact (@lem3343082 _87075 g x). Qed.
Lemma lem3343084 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (x : _87075 -> Prop) : (term18 _87075 f x g) = (term19 _87075 f g x).
Proof. exact (MK_COMB (@lem3343079 _87075 f x) (@lem3343083 _87075 g x)). Qed.
Lemma lem3343087 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term20 _87075 f g) = (term21 _87075 f g).
Proof. exact (fun_ext (fun x : _87075 -> Prop => @lem3343084 _87075 f g x)). Qed.
Lemma lem3343088 {_87075 : Type'} : (@all (_87075 -> Prop)) = (@all (_87075 -> Prop)).
Proof. exact (eq_refl (@all (_87075 -> Prop))). Qed.
Lemma lem3343089 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term1 _87075 f g) = (term22 _87075 f g).
Proof. exact (MK_COMB (@lem3343088 _87075) (@lem3343087 _87075 f g)). Qed.
Lemma lem3343094 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3343095 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term3 _87075 f g) = (term23 _87075 f g).
Proof. exact (MK_COMB (@lem3343094) (@lem3343089 _87075 f g)). Qed.
Lemma lem3343103 {A : Type'} (s : type686 A) (x : A) : (term24 A x s) = (term25 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3343104 {_87075 : Type'} (s : type686 _87075) (x : _87075) : (term24 _87075 x s) = (term25 _87075 s x).
Proof. exact (@lem3343103 _87075 s x). Qed.
Lemma lem3343105 {_87075 : Type'} (f : type686 _87075) (x : _87075) : (term24 _87075 x f) = (term25 _87075 f x).
Proof. exact (@lem3343104 _87075 f x). Qed.
Lemma lem3343113 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3343114 {_87075 : Type'} (P : type686 _87075) (x : _87075 -> Prop) : (@IN (_87075 -> Prop) x P) = (P x).
Proof. exact (@lem3343113 (_87075 -> Prop) P x). Qed.
Lemma lem3343115 {_87075 : Type'} (f : type686 _87075) (t : _87075 -> Prop) : (@IN (_87075 -> Prop) t f) = (f t).
Proof. exact (@lem3343114 _87075 f t). Qed.
Lemma lem3343116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3343117 {_87075 : Type'} (f : type686 _87075) (t : _87075 -> Prop) : (term26 _87075 t f) = (term27 _87075 f t).
Proof. exact (MK_COMB (@lem3343116) (@lem3343115 _87075 f t)). Qed.
Lemma lem3343119 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3343120 {_87075 : Type'} (P : _87075 -> Prop) (x : _87075) : (@IN _87075 x P) = (P x).
Proof. exact (@lem3343119 _87075 P x). Qed.
Lemma lem3343121 {_87075 : Type'} (t : _87075 -> Prop) (x : _87075) : (@IN _87075 x t) = (t x).
Proof. exact (@lem3343120 _87075 t x). Qed.
Lemma lem3343122 {_87075 : Type'} (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) : (term28 _87075 f x t) = (term29 _87075 f t x).
Proof. exact (MK_COMB (@lem3343117 _87075 f t) (@lem3343121 _87075 t x)). Qed.
Lemma lem3343125 {_87075 : Type'} (f : type686 _87075) (x : _87075) : (term30 _87075 f x) = (term31 _87075 f x).
Proof. exact (fun_ext (fun t : _87075 -> Prop => @lem3343122 _87075 f t x)). Qed.
Lemma lem3343126 {_87075 : Type'} : (@ex (_87075 -> Prop)) = (@ex (_87075 -> Prop)).
Proof. exact (eq_refl (@ex (_87075 -> Prop))). Qed.
Lemma lem3343127 {_87075 : Type'} (f : type686 _87075) (x : _87075) : (term25 _87075 f x) = (term32 _87075 f x).
Proof. exact (MK_COMB (@lem3343126 _87075) (@lem3343125 _87075 f x)). Qed.
Lemma lem3343132 {_87075 : Type'} (f : type686 _87075) (x : _87075) : (term24 _87075 x f) = (term32 _87075 f x).
Proof. exact (TRANS (@lem3343105 _87075 f x) (@lem3343127 _87075 f x)). Qed.
Lemma lem3343133 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3343134 {_87075 : Type'} (f : type686 _87075) (x : _87075) : (term33 _87075 x f) = (term34 _87075 f x).
Proof. exact (MK_COMB (@lem3343133) (@lem3343132 _87075 f x)). Qed.
Lemma lem3343136 {A : Type'} (s : type686 A) (x : A) : (term24 A x s) = (term25 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3343137 {_87075 : Type'} (s : type686 _87075) (x : _87075) : (term24 _87075 x s) = (term25 _87075 s x).
Proof. exact (@lem3343136 _87075 s x). Qed.
Lemma lem3343138 {_87075 : Type'} (g : type686 _87075) (x : _87075) : (term24 _87075 x g) = (term25 _87075 g x).
Proof. exact (@lem3343137 _87075 g x). Qed.
Lemma lem3343146 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3343147 {_87075 : Type'} (P : type686 _87075) (x : _87075 -> Prop) : (@IN (_87075 -> Prop) x P) = (P x).
Proof. exact (@lem3343146 (_87075 -> Prop) P x). Qed.
Lemma lem3343148 {_87075 : Type'} (g : type686 _87075) (t : _87075 -> Prop) : (@IN (_87075 -> Prop) t g) = (g t).
Proof. exact (@lem3343147 _87075 g t). Qed.
Lemma lem3343149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3343150 {_87075 : Type'} (g : type686 _87075) (t : _87075 -> Prop) : (term26 _87075 t g) = (term27 _87075 g t).
Proof. exact (MK_COMB (@lem3343149) (@lem3343148 _87075 g t)). Qed.
Lemma lem3343152 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3343153 {_87075 : Type'} (P : _87075 -> Prop) (x : _87075) : (@IN _87075 x P) = (P x).
Proof. exact (@lem3343152 _87075 P x). Qed.
Lemma lem3343154 {_87075 : Type'} (t : _87075 -> Prop) (x : _87075) : (@IN _87075 x t) = (t x).
Proof. exact (@lem3343153 _87075 t x). Qed.
Lemma lem3343155 {_87075 : Type'} (g : type686 _87075) (t : _87075 -> Prop) (x : _87075) : (term28 _87075 g x t) = (term29 _87075 g t x).
Proof. exact (MK_COMB (@lem3343150 _87075 g t) (@lem3343154 _87075 t x)). Qed.
Lemma lem3343158 {_87075 : Type'} (g : type686 _87075) (x : _87075) : (term30 _87075 g x) = (term31 _87075 g x).
Proof. exact (fun_ext (fun t : _87075 -> Prop => @lem3343155 _87075 g t x)). Qed.
Lemma lem3343159 {_87075 : Type'} : (@ex (_87075 -> Prop)) = (@ex (_87075 -> Prop)).
Proof. exact (eq_refl (@ex (_87075 -> Prop))). Qed.
Lemma lem3343160 {_87075 : Type'} (g : type686 _87075) (x : _87075) : (term25 _87075 g x) = (term32 _87075 g x).
Proof. exact (MK_COMB (@lem3343159 _87075) (@lem3343158 _87075 g x)). Qed.
Lemma lem3343165 {_87075 : Type'} (g : type686 _87075) (x : _87075) : (term24 _87075 x g) = (term32 _87075 g x).
Proof. exact (TRANS (@lem3343138 _87075 g x) (@lem3343160 _87075 g x)). Qed.
Lemma lem3343166 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (x : _87075) : (term35 _87075 f x g) = (term36 _87075 f g x).
Proof. exact (MK_COMB (@lem3343134 _87075 f x) (@lem3343165 _87075 g x)). Qed.
Lemma lem3343169 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term37 _87075 f g) = (term38 _87075 f g).
Proof. exact (fun_ext (fun x : _87075 => @lem3343166 _87075 f g x)). Qed.
Lemma lem3343170 {_87075 : Type'} : (@all _87075) = (@all _87075).
Proof. exact (eq_refl (@all _87075)). Qed.
Lemma lem3343171 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term5 _87075 f g) = (term39 _87075 f g).
Proof. exact (MK_COMB (@lem3343170 _87075) (@lem3343169 _87075 f g)). Qed.
Lemma lem3343176 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term7 _87075 f g) = (term40 _87075 f g).
Proof. exact (MK_COMB (@lem3343095 _87075 f g) (@lem3343171 _87075 f g)). Qed.
Lemma lem3343179 {_87075 : Type'} (f : type686 _87075) : (term9 _87075 f) = (term41 _87075 f).
Proof. exact (fun_ext (fun g : type686 _87075 => @lem3343176 _87075 f g)). Qed.
Lemma lem3343180 {_87075 : Type'} : (@all ((_87075 -> Prop) -> Prop)) = (@all ((_87075 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87075 -> Prop) -> Prop))). Qed.
Lemma lem3343181 {_87075 : Type'} (f : type686 _87075) : (term11 _87075 f) = (term42 _87075 f).
Proof. exact (MK_COMB (@lem3343180 _87075) (@lem3343179 _87075 f)). Qed.
Lemma lem3343186 {_87075 : Type'} : (term13 _87075) = (term43 _87075).
Proof. exact (fun_ext (fun f : type686 _87075 => @lem3343181 _87075 f)). Qed.
Lemma lem3343187 {_87075 : Type'} : (@all ((_87075 -> Prop) -> Prop)) = (@all ((_87075 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87075 -> Prop) -> Prop))). Qed.
Lemma lem3343188 {_87075 : Type'} : (term15 _87075) = (term44 _87075).
Proof. exact (MK_COMB (@lem3343187 _87075) (@lem3343186 _87075)). Qed.
Lemma lem3343193 {_87075 : Type'} : (term44 _87075) = (term15 _87075).
Proof. exact (SYM (@lem3343188 _87075)). Qed.
Lemma lem3343195 (p : Prop) : p = (term45 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3343196 {_87075 : Type'} : (term44 _87075) = (term46 _87075).
Proof. exact (@lem3343195 (term44 _87075)). Qed.
Lemma lem3343197 {_87075 : Type'} : (term46 _87075) = (term44 _87075).
Proof. exact (SYM (@lem3343196 _87075)). Qed.
Lemma lem3343198 {_87075 : Type'} (h1 : term47 _87075) : term47 _87075.
Proof. exact (h1). Qed.
Lemma lem3343201 {_87075 : Type'} (h1 : term46 _87075) : term46 _87075.
Proof. exact (h1). Qed.
Lemma lem3343202 {_87075 : Type'} : term48 _87075.
Proof. exact (fun h0 : term46 _87075 => @lem3343201 _87075 h0). Qed.
Lemma lem3343203 {_87075 : Type'} (h1 : term48 _87075) : term48 _87075.
Proof. exact (h1). Qed.
Lemma lem3343204 {_87075 : Type'} (h1 : term46 _87075) : term46 _87075.
Proof. exact (h1). Qed.
Lemma lem3343205 {_87075 : Type'} (h1 : term46 _87075) (h2 : term48 _87075) : term46 _87075.
Proof. exact (@lem3343203 _87075 h2 (@lem3343204 _87075 h1)). Qed.
Lemma lem3343206 {_87075 : Type'} (h1 : term46 _87075) : term49 _87075.
Proof. exact (fun h0 : term48 _87075 => @lem3343205 _87075 h1 h0). Qed.
Lemma lem3343207 {_87075 : Type'} (h1 : term48 _87075) : term48 _87075.
Proof. exact (h1). Qed.
Lemma lem3343208 {_87075 : Type'} (h1 : term46 _87075) (h2 : term48 _87075) : term46 _87075.
Proof. exact (@lem3343206 _87075 h1 (@lem3343207 _87075 h2)). Qed.
Lemma lem3343209 {_87075 : Type'} (h1 : term48 _87075) : term48 _87075.
Proof. exact (fun h0 : term46 _87075 => @lem3343208 _87075 h0 h1). Qed.
Lemma lem3343210 {_87075 : Type'} : term50 _87075.
Proof. exact (fun h0 : term48 _87075 => @lem3343209 _87075 h0). Qed.
Lemma lem3343213 {_87075 : Type'} : term48 _87075.
Proof. exact (@lem3343210 _87075 (@lem3343202 _87075)). Qed.
Lemma lem3343214 {_87075 : Type'} : term48 _87075.
Proof. exact (@lem3343213 _87075). Qed.
Lemma lem3343216 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3343217 {_87075 : Type'} : (term46 _87075) = (term51 _87075).
Proof. exact (@lem3343216 (term47 _87075)). Qed.
Lemma lem3343219 (t : Prop) : (term52 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3343220 {_87075 : Type'} : (term51 _87075) = (term44 _87075).
Proof. exact (@lem3343219 (term44 _87075)). Qed.
Lemma lem3343307 {_87075 : Type'} : (term46 _87075) = (term44 _87075).
Proof. exact (TRANS (@lem3343217 _87075) (@lem3343220 _87075)). Qed.
Lemma lem3343312 {_87075 : Type'} (g : type686 _87075) (t : _87075 -> Prop) (x : _87075) : (term29 _87075 g t x) = (term29 _87075 g t x).
Proof. exact (eq_refl (term29 _87075 g t x)). Qed.
Lemma lem3343313 {_87075 : Type'} (g : type686 _87075) (x : _87075) : (term31 _87075 g x) = (term31 _87075 g x).
Proof. exact (fun_ext (fun t : _87075 -> Prop => @lem3343312 _87075 g t x)). Qed.
Lemma lem3343314 {_87075 : Type'} : (@ex (_87075 -> Prop)) = (@ex (_87075 -> Prop)).
Proof. exact (eq_refl (@ex (_87075 -> Prop))). Qed.
Lemma lem3343315 {_87075 : Type'} (g : type686 _87075) (x : _87075) : (term32 _87075 g x) = (term32 _87075 g x).
Proof. exact (MK_COMB (@lem3343314 _87075) (@lem3343313 _87075 g x)). Qed.
Lemma lem3343320 {_87075 : Type'} (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) : (term29 _87075 f t x) = (term29 _87075 f t x).
Proof. exact (eq_refl (term29 _87075 f t x)). Qed.
Lemma lem3343321 {_87075 : Type'} (f : type686 _87075) (x : _87075) : (term31 _87075 f x) = (term31 _87075 f x).
Proof. exact (fun_ext (fun t : _87075 -> Prop => @lem3343320 _87075 f t x)). Qed.
Lemma lem3343322 {_87075 : Type'} : (@ex (_87075 -> Prop)) = (@ex (_87075 -> Prop)).
Proof. exact (eq_refl (@ex (_87075 -> Prop))). Qed.
Lemma lem3343323 {_87075 : Type'} (f : type686 _87075) (x : _87075) : (term32 _87075 f x) = (term32 _87075 f x).
Proof. exact (MK_COMB (@lem3343322 _87075) (@lem3343321 _87075 f x)). Qed.
Lemma lem3343324 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3343325 {_87075 : Type'} (f : type686 _87075) (x : _87075) : (term34 _87075 f x) = (term34 _87075 f x).
Proof. exact (MK_COMB (@lem3343324) (@lem3343323 _87075 f x)). Qed.
Lemma lem3343326 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (x : _87075) : (term36 _87075 f g x) = (term36 _87075 f g x).
Proof. exact (MK_COMB (@lem3343325 _87075 f x) (@lem3343315 _87075 g x)). Qed.
Lemma lem3343327 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term38 _87075 f g) = (term38 _87075 f g).
Proof. exact (fun_ext (fun x : _87075 => @lem3343326 _87075 f g x)). Qed.
Lemma lem3343328 {_87075 : Type'} : (@all _87075) = (@all _87075).
Proof. exact (eq_refl (@all _87075)). Qed.
Lemma lem3343329 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term39 _87075 f g) = (term39 _87075 f g).
Proof. exact (MK_COMB (@lem3343328 _87075) (@lem3343327 _87075 f g)). Qed.
Lemma lem3343334 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (x : _87075 -> Prop) : (term19 _87075 f g x) = (term19 _87075 f g x).
Proof. exact (eq_refl (term19 _87075 f g x)). Qed.
Lemma lem3343335 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term21 _87075 f g) = (term21 _87075 f g).
Proof. exact (fun_ext (fun x : _87075 -> Prop => @lem3343334 _87075 f g x)). Qed.
Lemma lem3343336 {_87075 : Type'} : (@all (_87075 -> Prop)) = (@all (_87075 -> Prop)).
Proof. exact (eq_refl (@all (_87075 -> Prop))). Qed.
Lemma lem3343337 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term22 _87075 f g) = (term22 _87075 f g).
Proof. exact (MK_COMB (@lem3343336 _87075) (@lem3343335 _87075 f g)). Qed.
Lemma lem3343338 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3343339 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term23 _87075 f g) = (term23 _87075 f g).
Proof. exact (MK_COMB (@lem3343338) (@lem3343337 _87075 f g)). Qed.
Lemma lem3343340 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term40 _87075 f g) = (term40 _87075 f g).
Proof. exact (MK_COMB (@lem3343339 _87075 f g) (@lem3343329 _87075 f g)). Qed.
Lemma lem3343341 {_87075 : Type'} (f : type686 _87075) : (term41 _87075 f) = (term41 _87075 f).
Proof. exact (fun_ext (fun g : type686 _87075 => @lem3343340 _87075 f g)). Qed.
Lemma lem3343342 {_87075 : Type'} : (@all ((_87075 -> Prop) -> Prop)) = (@all ((_87075 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87075 -> Prop) -> Prop))). Qed.
Lemma lem3343343 {_87075 : Type'} (f : type686 _87075) : (term42 _87075 f) = (term42 _87075 f).
Proof. exact (MK_COMB (@lem3343342 _87075) (@lem3343341 _87075 f)). Qed.
Lemma lem3343344 {_87075 : Type'} : (term43 _87075) = (term43 _87075).
Proof. exact (fun_ext (fun f : type686 _87075 => @lem3343343 _87075 f)). Qed.
Lemma lem3343345 {_87075 : Type'} : (@all ((_87075 -> Prop) -> Prop)) = (@all ((_87075 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87075 -> Prop) -> Prop))). Qed.
Lemma lem3343346 {_87075 : Type'} : (term44 _87075) = (term44 _87075).
Proof. exact (MK_COMB (@lem3343345 _87075) (@lem3343344 _87075)). Qed.
Lemma lem3343395 {_87075 : Type'} : (term46 _87075) = (term44 _87075).
Proof. exact (TRANS (@lem3343307 _87075) (@lem3343346 _87075)). Qed.
Lemma lem3343396 {_87075 : Type'} : (term44 _87075) = (term46 _87075).
Proof. exact (SYM (@lem3343395 _87075)). Qed.
Lemma lem3343397 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (h1 : term22 _87075 f g) : term22 _87075 f g.
Proof. exact (h1). Qed.
Lemma lem3343398 {_87075 : Type'} (f : type686 _87075) (x : _87075) (h1 : term32 _87075 f x) : term32 _87075 f x.
Proof. exact (h1). Qed.
Lemma lem3343400 (p : Prop) : p = (term45 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3343401 {_87075 : Type'} (g : type686 _87075) (x : _87075) : (term32 _87075 g x) = (term53 _87075 g x).
Proof. exact (@lem3343400 (term32 _87075 g x)). Qed.
Lemma lem3343402 {_87075 : Type'} (g : type686 _87075) (x : _87075) : (term53 _87075 g x) = (term32 _87075 g x).
Proof. exact (SYM (@lem3343401 _87075 g x)). Qed.
Lemma lem3343403 {_87075 : Type'} (g : type686 _87075) (x : _87075) (h1 : term54 _87075 g x) : term54 _87075 g x.
Proof. exact (h1). Qed.
Lemma lem3343410 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (x : _87075 -> Prop) : (term19 _87075 f g x) = (term55 _87075 f g x).
Proof. exact (@lem17265 (f x) (g x)). Qed.
Lemma lem3343411 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term21 _87075 f g) = (term56 _87075 f g).
Proof. exact (fun_ext (fun x : _87075 -> Prop => @lem3343410 _87075 f g x)). Qed.
Lemma lem3343412 {_87075 : Type'} : (@all (_87075 -> Prop)) = (@all (_87075 -> Prop)).
Proof. exact (eq_refl (@all (_87075 -> Prop))). Qed.
Lemma lem3343449 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term22 _87075 f g) = (term57 _87075 f g).
Proof. exact (MK_COMB (@lem3343412 _87075) (@lem3343411 _87075 f g)). Qed.
Lemma lem3343450 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (h1 : term22 _87075 f g) : term57 _87075 f g.
Proof. exact (EQ_MP (@lem3343449 _87075 f g) (@lem3343397 _87075 f g h1)). Qed.
Lemma lem3343455 {_87075 : Type'} (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) : (term29 _87075 f t x) = (term29 _87075 f t x).
Proof. exact (eq_refl (term29 _87075 f t x)). Qed.
Lemma lem3343456 {_87075 : Type'} (f : type686 _87075) (x : _87075) : (term31 _87075 f x) = (term31 _87075 f x).
Proof. exact (fun_ext (fun t : _87075 -> Prop => @lem3343455 _87075 f t x)). Qed.
Lemma lem3343457 {_87075 : Type'} : (@ex (_87075 -> Prop)) = (@ex (_87075 -> Prop)).
Proof. exact (eq_refl (@ex (_87075 -> Prop))). Qed.
Lemma lem3343490 {_87075 : Type'} (f : type686 _87075) (x : _87075) : (term32 _87075 f x) = (term32 _87075 f x).
Proof. exact (MK_COMB (@lem3343457 _87075) (@lem3343456 _87075 f x)). Qed.
Lemma lem3343491 {_87075 : Type'} (f : type686 _87075) (x : _87075) (h1 : term32 _87075 f x) : term32 _87075 f x.
Proof. exact (EQ_MP (@lem3343490 _87075 f x) (@lem3343398 _87075 f x h1)). Qed.
Lemma lem3343498 {_87075 : Type'} (g : type686 _87075) (t : _87075 -> Prop) (x : _87075) : (term58 _87075 g t x) = (term59 _87075 g t x).
Proof. exact (@lem17045 (g t) (t x)). Qed.
Lemma lem3343499 {_87075 : Type'} (P : type686 _87075) : (term60 _87075 P) = (term61 _87075 P).
Proof. exact (@lem18394 (_87075 -> Prop) P). Qed.
Lemma lem3343500 {_87075 : Type'} (g : type686 _87075) (x : _87075) : (term54 _87075 g x) = (term62 _87075 g x).
Proof. exact (@lem3343499 _87075 (term31 _87075 g x)). Qed.
Lemma lem3343501 {_87075 : Type'} (g : type686 _87075) (t : _87075 -> Prop) (x : _87075) : (term63 _87075 g x t) = (term29 _87075 g t x).
Proof. exact (eq_refl (term63 _87075 g x t)). Qed.
Lemma lem3343502 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3343503 {_87075 : Type'} (g : type686 _87075) (t : _87075 -> Prop) (x : _87075) : (term64 _87075 g x t) = (term58 _87075 g t x).
Proof. exact (MK_COMB (@lem3343502) (@lem3343501 _87075 g t x)). Qed.
Lemma lem3343504 {_87075 : Type'} (g : type686 _87075) (t : _87075 -> Prop) (x : _87075) : (term64 _87075 g x t) = (term59 _87075 g t x).
Proof. exact (TRANS (@lem3343503 _87075 g t x) (@lem3343498 _87075 g t x)). Qed.
Lemma lem3343505 {_87075 : Type'} (g : type686 _87075) (x : _87075) : (term65 _87075 g x) = (term66 _87075 g x).
Proof. exact (fun_ext (fun t : _87075 -> Prop => @lem3343504 _87075 g t x)). Qed.
Lemma lem3343506 {_87075 : Type'} : (@all (_87075 -> Prop)) = (@all (_87075 -> Prop)).
Proof. exact (eq_refl (@all (_87075 -> Prop))). Qed.
Lemma lem3343507 {_87075 : Type'} (g : type686 _87075) (x : _87075) : (term62 _87075 g x) = (term67 _87075 g x).
Proof. exact (MK_COMB (@lem3343506 _87075) (@lem3343505 _87075 g x)). Qed.
Lemma lem3343560 {_87075 : Type'} (g : type686 _87075) (x : _87075) : (term54 _87075 g x) = (term67 _87075 g x).
Proof. exact (TRANS (@lem3343500 _87075 g x) (@lem3343507 _87075 g x)). Qed.
Lemma lem3343561 {_87075 : Type'} (g : type686 _87075) (x : _87075) (h1 : term54 _87075 g x) : term67 _87075 g x.
Proof. exact (EQ_MP (@lem3343560 _87075 g x) (@lem3343403 _87075 g x h1)). Qed.
Lemma lem3343562 {_87075 : Type'} (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) (h1 : term29 _87075 f t x) : term29 _87075 f t x.
Proof. exact (h1). Qed.
Lemma lem3343567 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3343568 {_87075 : Type'} (f : type686 _87075) (x : _87075 -> Prop) : (f x) = (@I ((_87075 -> Prop) -> Prop) f x).
Proof. exact (@lem3343567 (_87075 -> Prop) Prop f x). Qed.
Lemma lem3343570 {_87075 : Type'} (g : type686 _87075) (x : _87075 -> Prop) : (g x) = (@I ((_87075 -> Prop) -> Prop) g x).
Proof. exact (@lem3343568 _87075 g x). Qed.
Lemma lem3343571 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3343576 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3343578 {_87075 : Type'} (f : type686 _87075) (x : _87075 -> Prop) : (f x) = (@I ((_87075 -> Prop) -> Prop) f x).
Proof. exact (@lem3343576 (_87075 -> Prop) Prop f x). Qed.
Lemma lem3343579 {_87075 : Type'} (f : type686 _87075) (x : _87075 -> Prop) : (term68 _87075 f x) = (term69 _87075 f x).
Proof. exact (MK_COMB (@lem3343571) (@lem3343578 _87075 f x)). Qed.
Lemma lem3343580 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3343581 {_87075 : Type'} (f : type686 _87075) (x : _87075 -> Prop) : (term70 _87075 f x) = (term71 _87075 f x).
Proof. exact (MK_COMB (@lem3343580) (@lem3343579 _87075 f x)). Qed.
Lemma lem3343582 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (x : _87075 -> Prop) : (term55 _87075 f g x) = (term72 _87075 f g x).
Proof. exact (MK_COMB (@lem3343581 _87075 f x) (@lem3343570 _87075 g x)). Qed.
Lemma lem3343583 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term56 _87075 f g) = (term73 _87075 f g).
Proof. exact (fun_ext (fun x : _87075 -> Prop => @lem3343582 _87075 f g x)). Qed.
Lemma lem3343584 {_87075 : Type'} : (@all (_87075 -> Prop)) = (@all (_87075 -> Prop)).
Proof. exact (eq_refl (@all (_87075 -> Prop))). Qed.
Lemma lem3343585 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term57 _87075 f g) = (term74 _87075 f g).
Proof. exact (MK_COMB (@lem3343584 _87075) (@lem3343583 _87075 f g)). Qed.
Lemma lem3343586 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (h1 : term22 _87075 f g) : term74 _87075 f g.
Proof. exact (EQ_MP (@lem3343585 _87075 f g) (@lem3343450 _87075 f g h1)). Qed.
Lemma lem3343587 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3343592 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3343593 {_87075 : Type'} (f : _87075 -> Prop) (x : _87075) : (f x) = (@I (_87075 -> Prop) f x).
Proof. exact (@lem3343592 _87075 Prop f x). Qed.
Lemma lem3343595 {_87075 : Type'} (t : _87075 -> Prop) (x : _87075) : (t x) = (@I (_87075 -> Prop) t x).
Proof. exact (@lem3343593 _87075 t x). Qed.
Lemma lem3343596 {_87075 : Type'} (t : _87075 -> Prop) (x : _87075) : (term75 _87075 t x) = (term76 _87075 t x).
Proof. exact (MK_COMB (@lem3343587) (@lem3343595 _87075 t x)). Qed.
Lemma lem3343597 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3343602 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3343603 {_87075 : Type'} (f : type686 _87075) (x : _87075 -> Prop) : (f x) = (@I ((_87075 -> Prop) -> Prop) f x).
Proof. exact (@lem3343602 (_87075 -> Prop) Prop f x). Qed.
Lemma lem3343605 {_87075 : Type'} (g : type686 _87075) (t : _87075 -> Prop) : (g t) = (@I ((_87075 -> Prop) -> Prop) g t).
Proof. exact (@lem3343603 _87075 g t). Qed.
Lemma lem3343606 {_87075 : Type'} (g : type686 _87075) (t : _87075 -> Prop) : (term68 _87075 g t) = (term69 _87075 g t).
Proof. exact (MK_COMB (@lem3343597) (@lem3343605 _87075 g t)). Qed.
Lemma lem3343607 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3343608 {_87075 : Type'} (g : type686 _87075) (t : _87075 -> Prop) : (term70 _87075 g t) = (term71 _87075 g t).
Proof. exact (MK_COMB (@lem3343607) (@lem3343606 _87075 g t)). Qed.
Lemma lem3343609 {_87075 : Type'} (g : type686 _87075) (t : _87075 -> Prop) (x : _87075) : (term59 _87075 g t x) = (term77 _87075 g t x).
Proof. exact (MK_COMB (@lem3343608 _87075 g t) (@lem3343596 _87075 t x)). Qed.
Lemma lem3343610 {_87075 : Type'} (g : type686 _87075) (x : _87075) : (term66 _87075 g x) = (term78 _87075 g x).
Proof. exact (fun_ext (fun t : _87075 -> Prop => @lem3343609 _87075 g t x)). Qed.
Lemma lem3343611 {_87075 : Type'} : (@all (_87075 -> Prop)) = (@all (_87075 -> Prop)).
Proof. exact (eq_refl (@all (_87075 -> Prop))). Qed.
Lemma lem3343612 {_87075 : Type'} (g : type686 _87075) (x : _87075) : (term67 _87075 g x) = (term79 _87075 g x).
Proof. exact (MK_COMB (@lem3343611 _87075) (@lem3343610 _87075 g x)). Qed.
Lemma lem3343613 {_87075 : Type'} (g : type686 _87075) (x : _87075) (h1 : term54 _87075 g x) : term79 _87075 g x.
Proof. exact (EQ_MP (@lem3343612 _87075 g x) (@lem3343561 _87075 g x h1)). Qed.
Lemma lem3343618 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3343619 {_87075 : Type'} (f : _87075 -> Prop) (x : _87075) : (f x) = (@I (_87075 -> Prop) f x).
Proof. exact (@lem3343618 _87075 Prop f x). Qed.
Lemma lem3343621 {_87075 : Type'} (t : _87075 -> Prop) (x : _87075) : (t x) = (@I (_87075 -> Prop) t x).
Proof. exact (@lem3343619 _87075 t x). Qed.
Lemma lem3343626 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3343627 {_87075 : Type'} (f : type686 _87075) (x : _87075 -> Prop) : (f x) = (@I ((_87075 -> Prop) -> Prop) f x).
Proof. exact (@lem3343626 (_87075 -> Prop) Prop f x). Qed.
Lemma lem3343629 {_87075 : Type'} (f : type686 _87075) (t : _87075 -> Prop) : (f t) = (@I ((_87075 -> Prop) -> Prop) f t).
Proof. exact (@lem3343627 _87075 f t). Qed.
Lemma lem3343630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3343631 {_87075 : Type'} (f : type686 _87075) (t : _87075 -> Prop) : (term27 _87075 f t) = (term80 _87075 f t).
Proof. exact (MK_COMB (@lem3343630) (@lem3343629 _87075 f t)). Qed.
Lemma lem3343632 {_87075 : Type'} (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) : (term29 _87075 f t x) = (term81 _87075 f t x).
Proof. exact (MK_COMB (@lem3343631 _87075 f t) (@lem3343621 _87075 t x)). Qed.
Lemma lem3343633 {_87075 : Type'} (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) (h1 : term29 _87075 f t x) : term81 _87075 f t x.
Proof. exact (EQ_MP (@lem3343632 _87075 f t x) (@lem3343562 _87075 f t x h1)). Qed.
Lemma lem3343643 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (x : _87075 -> Prop) : (term72 _87075 f g x) = (term72 _87075 f g x).
Proof. exact (eq_refl (term72 _87075 f g x)). Qed.
Lemma lem3343644 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term73 _87075 f g) = (term73 _87075 f g).
Proof. exact (fun_ext (fun x : _87075 -> Prop => @lem3343643 _87075 f g x)). Qed.
Lemma lem3343645 {_87075 : Type'} : (@all (_87075 -> Prop)) = (@all (_87075 -> Prop)).
Proof. exact (eq_refl (@all (_87075 -> Prop))). Qed.
Lemma lem3343647 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term74 _87075 f g) = (term74 _87075 f g).
Proof. exact (MK_COMB (@lem3343645 _87075) (@lem3343644 _87075 f g)). Qed.
Lemma lem3343648 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (h1 : term22 _87075 f g) : term74 _87075 f g.
Proof. exact (EQ_MP (@lem3343647 _87075 f g) (@lem3343586 _87075 f g h1)). Qed.
Lemma lem3343656 {_87075 : Type'} (g : type686 _87075) (t : _87075 -> Prop) (x : _87075) : (term77 _87075 g t x) = (term77 _87075 g t x).
Proof. exact (eq_refl (term77 _87075 g t x)). Qed.
Lemma lem3343657 {_87075 : Type'} (g : type686 _87075) (x : _87075) : (term78 _87075 g x) = (term78 _87075 g x).
Proof. exact (fun_ext (fun t : _87075 -> Prop => @lem3343656 _87075 g t x)). Qed.
Lemma lem3343658 {_87075 : Type'} : (@all (_87075 -> Prop)) = (@all (_87075 -> Prop)).
Proof. exact (eq_refl (@all (_87075 -> Prop))). Qed.
Lemma lem3343660 {_87075 : Type'} (g : type686 _87075) (x : _87075) : (term79 _87075 g x) = (term79 _87075 g x).
Proof. exact (MK_COMB (@lem3343658 _87075) (@lem3343657 _87075 g x)). Qed.
Lemma lem3343661 {_87075 : Type'} (g : type686 _87075) (x : _87075) (h1 : term54 _87075 g x) : term79 _87075 g x.
Proof. exact (EQ_MP (@lem3343660 _87075 g x) (@lem3343613 _87075 g x h1)). Qed.
Lemma lem3343670 {_87075 : Type'} (_34891 : _87075 -> Prop) (f : type686 _87075) (g : type686 _87075) (h1 : term22 _87075 f g) : term82 _87075 f g _34891.
Proof. exact (@lem3343648 _87075 f g h1 _34891). Qed.
Lemma lem3343671 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (_34891 : _87075 -> Prop) : (term82 _87075 f g _34891) = (term72 _87075 f g _34891).
Proof. exact (eq_refl (term82 _87075 f g _34891)). Qed.
Lemma lem3343673 {_87075 : Type'} (_34892 : _87075 -> Prop) (g : type686 _87075) (x : _87075) (h1 : term54 _87075 g x) : term83 _87075 g x _34892.
Proof. exact (@lem3343661 _87075 g x h1 _34892). Qed.
Lemma lem3343674 {_87075 : Type'} (g : type686 _87075) (_34892 : _87075 -> Prop) (x : _87075) : (term83 _87075 g x _34892) = (term77 _87075 g _34892 x).
Proof. exact (eq_refl (term83 _87075 g x _34892)). Qed.
Lemma lem3343681 {_87075 : Type'} (_34891 : _87075 -> Prop) (f : type686 _87075) (g : type686 _87075) (h1 : term22 _87075 f g) : term72 _87075 f g _34891.
Proof. exact (EQ_MP (@lem3343671 _87075 f g _34891) (@lem3343670 _87075 _34891 f g h1)). Qed.
Lemma lem3343687 {_87075 : Type'} (_34892 : _87075 -> Prop) (g : type686 _87075) (x : _87075) (h1 : term54 _87075 g x) : term77 _87075 g _34892 x.
Proof. exact (EQ_MP (@lem3343674 _87075 g _34892 x) (@lem3343673 _87075 _34892 g x h1)). Qed.
Lemma lem3343693 {_87075 : Type'} (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) (h1 : term29 _87075 f t x) : @I ((_87075 -> Prop) -> Prop) f t.
Proof. exact (proj1 (@lem3343633 _87075 f t x h1)). Qed.
Lemma lem3343694 {_87075 : Type'} (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) (h1 : term29 _87075 f t x) : term84 _87075 f t.
Proof. exact (fun h0 : term69 _87075 f t => @lem3343693 _87075 f t x h1). Qed.
Lemma lem3343696 (p : Prop) : (term85 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3343697 {_87075 : Type'} (f : type686 _87075) (t : _87075 -> Prop) : (term84 _87075 f t) = (@I ((_87075 -> Prop) -> Prop) f t).
Proof. exact (@lem3343696 (@I ((_87075 -> Prop) -> Prop) f t)). Qed.
Lemma lem3343698 {_87075 : Type'} (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) (h1 : term29 _87075 f t x) : @I ((_87075 -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem3343697 _87075 f t) (@lem3343694 _87075 f t x h1)). Qed.
Lemma lem3343704 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3343705 {_87075 : Type'} (g : type686 _87075) (f : type686 _87075) (_34891 : _87075 -> Prop) : (term72 _87075 f g _34891) = (term86 _87075 g f _34891).
Proof. exact (@lem3343704 (@I ((_87075 -> Prop) -> Prop) g _34891) (term69 _87075 f _34891)). Qed.
Lemma lem3343711 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3343712 {_87075 : Type'} (g : type686 _87075) (f : type686 _87075) (_34891 : _87075 -> Prop) : (term87 _87075 f g _34891) = (term88 _87075 g f _34891).
Proof. exact (MK_COMB (@lem3343711) (@lem3343705 _87075 g f _34891)). Qed.
Lemma lem3343718 {_87075 : Type'} (g : type686 _87075) (f : type686 _87075) (_34891 : _87075 -> Prop) : (term86 _87075 g f _34891) = (term86 _87075 g f _34891).
Proof. exact (eq_refl (term86 _87075 g f _34891)). Qed.
Lemma lem3343719 {_87075 : Type'} (g : type686 _87075) (f : type686 _87075) (_34891 : _87075 -> Prop) : ((term72 _87075 f g _34891) = (term86 _87075 g f _34891)) = ((term86 _87075 g f _34891) = (term86 _87075 g f _34891)).
Proof. exact (MK_COMB (@lem3343712 _87075 g f _34891) (@lem3343718 _87075 g f _34891)). Qed.
Lemma lem3343721 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3343722 (x : Prop) : (x = x) = True.
Proof. exact (@lem3343721 Prop x). Qed.
Lemma lem3343723 {_87075 : Type'} (g : type686 _87075) (f : type686 _87075) (_34891 : _87075 -> Prop) : ((term86 _87075 g f _34891) = (term86 _87075 g f _34891)) = True.
Proof. exact (@lem3343722 (term86 _87075 g f _34891)). Qed.
Lemma lem3343724 {_87075 : Type'} (g : type686 _87075) (f : type686 _87075) (_34891 : _87075 -> Prop) : ((term72 _87075 f g _34891) = (term86 _87075 g f _34891)) = True.
Proof. exact (TRANS (@lem3343719 _87075 g f _34891) (@lem3343723 _87075 g f _34891)). Qed.
Lemma lem3343725 {_87075 : Type'} (g : type686 _87075) (f : type686 _87075) (_34891 : _87075 -> Prop) : True = ((term72 _87075 f g _34891) = (term86 _87075 g f _34891)).
Proof. exact (SYM (@lem3343724 _87075 g f _34891)). Qed.
Lemma lem3343726 {_87075 : Type'} (g : type686 _87075) (f : type686 _87075) (_34891 : _87075 -> Prop) : (term72 _87075 f g _34891) = (term86 _87075 g f _34891).
Proof. exact (EQ_MP (@lem3343725 _87075 g f _34891) (@lem0)). Qed.
Lemma lem3343727 {_87075 : Type'} (_34891 : _87075 -> Prop) (f : type686 _87075) (g : type686 _87075) (h1 : term22 _87075 f g) : term86 _87075 g f _34891.
Proof. exact (EQ_MP (@lem3343726 _87075 g f _34891) (@lem3343681 _87075 _34891 f g h1)). Qed.
Lemma lem3343729 (b : Prop) (a : Prop) : (a \/ b) = (term89 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3343730 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (_34891 : _87075 -> Prop) : (term86 _87075 g f _34891) = (term90 _87075 f g _34891).
Proof. exact (@lem3343729 (term69 _87075 f _34891) (@I ((_87075 -> Prop) -> Prop) g _34891)). Qed.
Lemma lem3343732 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3343733 {_87075 : Type'} (f : type686 _87075) (_34891 : _87075 -> Prop) : (term91 _87075 f _34891) = (@I ((_87075 -> Prop) -> Prop) f _34891).
Proof. exact (@lem3343732 (@I ((_87075 -> Prop) -> Prop) f _34891)). Qed.
Lemma lem3343734 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3343735 {_87075 : Type'} (f : type686 _87075) (_34891 : _87075 -> Prop) : (term92 _87075 f _34891) = (term93 _87075 f _34891).
Proof. exact (MK_COMB (@lem3343734) (@lem3343733 _87075 f _34891)). Qed.
Lemma lem3343736 {_87075 : Type'} (g : type686 _87075) (_34891 : _87075 -> Prop) : (@I ((_87075 -> Prop) -> Prop) g _34891) = (@I ((_87075 -> Prop) -> Prop) g _34891).
Proof. exact (eq_refl (@I ((_87075 -> Prop) -> Prop) g _34891)). Qed.
Lemma lem3343737 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (_34891 : _87075 -> Prop) : (term90 _87075 f g _34891) = (term94 _87075 f g _34891).
Proof. exact (MK_COMB (@lem3343735 _87075 f _34891) (@lem3343736 _87075 g _34891)). Qed.
Lemma lem3343738 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (_34891 : _87075 -> Prop) : (term86 _87075 g f _34891) = (term94 _87075 f g _34891).
Proof. exact (TRANS (@lem3343730 _87075 f g _34891) (@lem3343737 _87075 f g _34891)). Qed.
Lemma lem3343741 {_87075 : Type'} (_34891 : _87075 -> Prop) (f : type686 _87075) (g : type686 _87075) (h1 : term22 _87075 f g) : term94 _87075 f g _34891.
Proof. exact (EQ_MP (@lem3343738 _87075 f g _34891) (@lem3343727 _87075 _34891 f g h1)). Qed.
Lemma lem3343742 {_87075 : Type'} (_34891 : _87075 -> Prop) (f : type686 _87075) (g : type686 _87075) (h1 : term22 _87075 f g) : term94 _87075 f g _34891.
Proof. exact (@lem3343741 _87075 _34891 f g h1). Qed.
Lemma lem3343743 {_87075 : Type'} (t : _87075 -> Prop) (f : type686 _87075) (g : type686 _87075) (h1 : term22 _87075 f g) : term94 _87075 f g t.
Proof. exact (@lem3343742 _87075 t f g h1). Qed.
Lemma lem3343746 {_87075 : Type'} (g : type686 _87075) (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) (h1 : term22 _87075 f g) (h2 : term29 _87075 f t x) : @I ((_87075 -> Prop) -> Prop) g t.
Proof. exact (@lem3343743 _87075 t f g h1 (@lem3343698 _87075 f t x h2)). Qed.
Lemma lem3343747 {_87075 : Type'} (g : type686 _87075) (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) (h1 : term22 _87075 f g) (h2 : term29 _87075 f t x) : term84 _87075 g t.
Proof. exact (fun h0 : term69 _87075 g t => @lem3343746 _87075 g f t x h1 h2). Qed.
Lemma lem3343749 (p : Prop) : (term85 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3343750 {_87075 : Type'} (g : type686 _87075) (t : _87075 -> Prop) : (term84 _87075 g t) = (@I ((_87075 -> Prop) -> Prop) g t).
Proof. exact (@lem3343749 (@I ((_87075 -> Prop) -> Prop) g t)). Qed.
Lemma lem3343751 {_87075 : Type'} (g : type686 _87075) (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) (h1 : term22 _87075 f g) (h2 : term29 _87075 f t x) : @I ((_87075 -> Prop) -> Prop) g t.
Proof. exact (EQ_MP (@lem3343750 _87075 g t) (@lem3343747 _87075 g f t x h1 h2)). Qed.
Lemma lem3343753 {_87075 : Type'} (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) (h1 : term29 _87075 f t x) : @I (_87075 -> Prop) t x.
Proof. exact (proj2 (@lem3343633 _87075 f t x h1)). Qed.
Lemma lem3343754 {_87075 : Type'} (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) (h1 : term29 _87075 f t x) : term95 _87075 t x.
Proof. exact (fun h0 : term76 _87075 t x => @lem3343753 _87075 f t x h1). Qed.
Lemma lem3343756 (p : Prop) : (term85 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3343757 {_87075 : Type'} (t : _87075 -> Prop) (x : _87075) : (term95 _87075 t x) = (@I (_87075 -> Prop) t x).
Proof. exact (@lem3343756 (@I (_87075 -> Prop) t x)). Qed.
Lemma lem3343758 {_87075 : Type'} (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) (h1 : term29 _87075 f t x) : @I (_87075 -> Prop) t x.
Proof. exact (EQ_MP (@lem3343757 _87075 t x) (@lem3343754 _87075 f t x h1)). Qed.
Lemma lem3343760 (a : Prop) (b : Prop) : (term96 a b) = (term97 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3343761 {_87075 : Type'} (g : type686 _87075) (_34892 : _87075 -> Prop) (x : _87075) : (term77 _87075 g _34892 x) = (term98 _87075 g _34892 x).
Proof. exact (@lem3343760 (@I ((_87075 -> Prop) -> Prop) g _34892) (@I (_87075 -> Prop) _34892 x)). Qed.
Lemma lem3343763 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3343764 {_87075 : Type'} (g : type686 _87075) (_34892 : _87075 -> Prop) (x : _87075) : (term98 _87075 g _34892 x) = (term99 _87075 g _34892 x).
Proof. exact (@lem3343763 (term81 _87075 g _34892 x)). Qed.
Lemma lem3343765 {_87075 : Type'} (g : type686 _87075) (_34892 : _87075 -> Prop) (x : _87075) : (term77 _87075 g _34892 x) = (term99 _87075 g _34892 x).
Proof. exact (TRANS (@lem3343761 _87075 g _34892 x) (@lem3343764 _87075 g _34892 x)). Qed.
Lemma lem3343767 {_87075 : Type'} (g : type686 _87075) (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) (h1 : term22 _87075 f g) (h2 : term29 _87075 f t x) : term81 _87075 g t x.
Proof. exact (conj (@lem3343751 _87075 g f t x h1 h2) (@lem3343758 _87075 f t x h2)). Qed.
Lemma lem3343769 {_87075 : Type'} (_34892 : _87075 -> Prop) (g : type686 _87075) (x : _87075) (h1 : term54 _87075 g x) : term99 _87075 g _34892 x.
Proof. exact (EQ_MP (@lem3343765 _87075 g _34892 x) (@lem3343687 _87075 _34892 g x h1)). Qed.
Lemma lem3343770 {_87075 : Type'} (_34892 : _87075 -> Prop) (g : type686 _87075) (x : _87075) (h1 : term54 _87075 g x) : term99 _87075 g _34892 x.
Proof. exact (@lem3343769 _87075 _34892 g x h1). Qed.
Lemma lem3343771 {_87075 : Type'} (t : _87075 -> Prop) (g : type686 _87075) (x : _87075) (h1 : term54 _87075 g x) : term99 _87075 g t x.
Proof. exact (@lem3343770 _87075 t g x h1). Qed.
Lemma lem3343774 {_87075 : Type'} (g : type686 _87075) (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) (h1 : term22 _87075 f g) (h2 : term54 _87075 g x) (h3 : term29 _87075 f t x) : False.
Proof. exact (@lem3343771 _87075 t g x h2 (@lem3343767 _87075 g f t x h1 h3)). Qed.
Lemma lem3343775 {_87075 : Type'} (g : type686 _87075) (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) (h1 : term22 _87075 f g) (h2 : term54 _87075 g x) (h3 : term29 _87075 f t x) : term100.
Proof. exact (fun h0 : ~ False => @lem3343774 _87075 g f t x h1 h2 h3). Qed.
Lemma lem3343777 (p : Prop) : (term85 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3343778 : term100 = False.
Proof. exact (@lem3343777 False). Qed.
Lemma lem3343779 {_87075 : Type'} (g : type686 _87075) (f : type686 _87075) (t : _87075 -> Prop) (x : _87075) (h1 : term22 _87075 f g) (h2 : term54 _87075 g x) (h3 : term29 _87075 f t x) : False.
Proof. exact (EQ_MP (@lem3343778) (@lem3343775 _87075 g f t x h1 h2 h3)). Qed.
Lemma lem3343780 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (x : _87075) (h1 : term22 _87075 f g) (h2 : term32 _87075 f x) (h3 : term54 _87075 g x) : False.
Proof. exact (ex_elim (@lem3343491 _87075 f x h2) (fun t : _87075 -> Prop => fun h0 : term31 _87075 f x t => @lem3343779 _87075 g f t x h1 h3 h0)). Qed.
Lemma lem3343781 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (x : _87075) (h1 : term22 _87075 f g) (h2 : term32 _87075 f x) (h3 : term54 _87075 g x) : (term32 _87075 f x) = False.
Proof. exact (prop_ext (fun h4 : term32 _87075 f x => @lem3343780 _87075 f g x h1 h2 h3) (fun h4 : False => @lem3343491 _87075 f x h2)). Qed.
Lemma lem3343782 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (x : _87075) (h1 : term22 _87075 f g) (h2 : term32 _87075 f x) (h3 : term54 _87075 g x) : False.
Proof. exact (EQ_MP (@lem3343781 _87075 f g x h1 h2 h3) (@lem3343491 _87075 f x h2)). Qed.
Lemma lem3343783 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (x : _87075) (h1 : term22 _87075 f g) (h2 : term32 _87075 f x) (h3 : term54 _87075 g x) : (term54 _87075 g x) = False.
Proof. exact (prop_ext (fun h4 : term54 _87075 g x => @lem3343782 _87075 f g x h1 h2 h3) (fun h4 : False => @lem3343403 _87075 g x h3)). Qed.
Lemma lem3343784 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (x : _87075) (h1 : term22 _87075 f g) (h2 : term32 _87075 f x) (h3 : term54 _87075 g x) : False.
Proof. exact (EQ_MP (@lem3343783 _87075 f g x h1 h2 h3) (@lem3343403 _87075 g x h3)). Qed.
Lemma lem3343785 {_87075 : Type'} (g : type686 _87075) (f : type686 _87075) (x : _87075) (h1 : term22 _87075 f g) (h2 : term32 _87075 f x) : term53 _87075 g x.
Proof. exact (fun h0 : term54 _87075 g x => @lem3343784 _87075 f g x h1 h2 h0). Qed.
Lemma lem3343786 {_87075 : Type'} (g : type686 _87075) (f : type686 _87075) (x : _87075) (h1 : term22 _87075 f g) (h2 : term32 _87075 f x) : term32 _87075 g x.
Proof. exact (EQ_MP (@lem3343402 _87075 g x) (@lem3343785 _87075 g f x h1 h2)). Qed.
Lemma lem3343787 {_87075 : Type'} (x : _87075) (f : type686 _87075) (g : type686 _87075) (h1 : term22 _87075 f g) : term36 _87075 f g x.
Proof. exact (fun h0 : term32 _87075 f x => @lem3343786 _87075 g f x h1 h0). Qed.
Lemma lem3343792 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (h1 : term22 _87075 f g) : term39 _87075 f g.
Proof. exact (fun x : _87075 => @lem3343787 _87075 x f g h1). Qed.
Lemma lem3343793 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : term40 _87075 f g.
Proof. exact (fun h0 : term22 _87075 f g => @lem3343792 _87075 f g h0). Qed.
Lemma lem3343798 {_87075 : Type'} (f : type686 _87075) : term42 _87075 f.
Proof. exact (fun g : type686 _87075 => @lem3343793 _87075 f g). Qed.
Lemma lem3343803 {_87075 : Type'} : term44 _87075.
Proof. exact (fun f : type686 _87075 => @lem3343798 _87075 f). Qed.
Lemma lem3343804 {_87075 : Type'} : term46 _87075.
Proof. exact (EQ_MP (@lem3343396 _87075) (@lem3343803 _87075)). Qed.
Lemma lem3343806 {_87075 : Type'} : term46 _87075.
Proof. exact (@lem3343214 _87075 (@lem3343804 _87075)). Qed.
Lemma lem3343807 {_87075 : Type'} (h1 : term47 _87075) : False.
Proof. exact (@lem3343806 _87075 (@lem3343198 _87075 h1)). Qed.
Lemma lem3343808 {_87075 : Type'} (h1 : term47 _87075) : (term47 _87075) = False.
Proof. exact (prop_ext (fun h2 : term47 _87075 => @lem3343807 _87075 h1) (fun h2 : False => @lem3343198 _87075 h1)). Qed.
Lemma lem3343809 {_87075 : Type'} (h1 : term47 _87075) : False.
Proof. exact (EQ_MP (@lem3343808 _87075 h1) (@lem3343198 _87075 h1)). Qed.
Lemma lem3343810 {_87075 : Type'} : term46 _87075.
Proof. exact (fun h0 : term47 _87075 => @lem3343809 _87075 h0). Qed.
Lemma lem3343811 {_87075 : Type'} : term44 _87075.
Proof. exact (EQ_MP (@lem3343197 _87075) (@lem3343810 _87075)). Qed.
Lemma lem3343812 {_87075 : Type'} : term15 _87075.
Proof. exact (EQ_MP (@lem3343193 _87075) (@lem3343811 _87075)). Qed.
Lemma lem3343813 {_87075 : Type'} : term14 _87075.
Proof. exact (EQ_MP (@lem3343057 _87075) (@lem3343812 _87075)). Qed.
