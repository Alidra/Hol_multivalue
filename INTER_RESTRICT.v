Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_RESTRICT_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3260097 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3260098 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) : (s = t) = (term0 _85450 s t).
Proof. exact (@lem3260097 _85450 s t). Qed.
Lemma lem3260099 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) : ((term1 _85450 s t P) = (term2 _85450 s t P)) = (term3 _85450 s t P).
Proof. exact (@lem3260098 _85450 (term1 _85450 s t P) (term2 _85450 s t P)). Qed.
Lemma lem3260126 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) : (term4 _85450 s P) = (term5 _85450 s P).
Proof. exact (fun_ext (fun t : _85450 -> Prop => @lem3260099 _85450 s t P)). Qed.
Lemma lem3260127 {_85450 : Type'} : (@all (_85450 -> Prop)) = (@all (_85450 -> Prop)).
Proof. exact (eq_refl (@all (_85450 -> Prop))). Qed.
Lemma lem3260128 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) : (term6 _85450 s P) = (term7 _85450 s P).
Proof. exact (MK_COMB (@lem3260127 _85450) (@lem3260126 _85450 s P)). Qed.
Lemma lem3260133 {_85450 : Type'} (P : _85450 -> Prop) : (term8 _85450 P) = (term9 _85450 P).
Proof. exact (fun_ext (fun s : _85450 -> Prop => @lem3260128 _85450 s P)). Qed.
Lemma lem3260134 {_85450 : Type'} : (@all (_85450 -> Prop)) = (@all (_85450 -> Prop)).
Proof. exact (eq_refl (@all (_85450 -> Prop))). Qed.
Lemma lem3260135 {_85450 : Type'} (P : _85450 -> Prop) : (term10 _85450 P) = (term11 _85450 P).
Proof. exact (MK_COMB (@lem3260134 _85450) (@lem3260133 _85450 P)). Qed.
Lemma lem3260140 {_85450 : Type'} : (term12 _85450) = (term13 _85450).
Proof. exact (fun_ext (fun P : _85450 -> Prop => @lem3260135 _85450 P)). Qed.
Lemma lem3260141 {_85450 : Type'} : (@all (_85450 -> Prop)) = (@all (_85450 -> Prop)).
Proof. exact (eq_refl (@all (_85450 -> Prop))). Qed.
Lemma lem3260142 {_85450 : Type'} : (term14 _85450) = (term15 _85450).
Proof. exact (MK_COMB (@lem3260141 _85450) (@lem3260140 _85450)). Qed.
Lemma lem3260147 {_85450 : Type'} : (term15 _85450) = (term14 _85450).
Proof. exact (SYM (@lem3260142 _85450)). Qed.
Lemma lem3260167 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term16 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3260168 {_85450 : Type'} (p : _85450 -> Prop) (x : _85450) : (term16 _85450 x p) = (p x).
Proof. exact (@lem3260167 _85450 p x). Qed.
Lemma lem3260169 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term17 _85450 x s t P) = (term18 _85450 s t P x).
Proof. exact (@lem3260168 _85450 (term19 _85450 s t P) x). Qed.
Lemma lem3260170 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term18 _85450 s t P x) = (term20 _85450 s t P x).
Proof. exact (eq_refl (term18 _85450 s t P x)). Qed.
Lemma lem3260171 {_85450 : Type'} (GEN_PVAR_15 : _85450) : (@SETSPEC _85450 GEN_PVAR_15) = (@SETSPEC _85450 GEN_PVAR_15).
Proof. exact (eq_refl (@SETSPEC _85450 GEN_PVAR_15)). Qed.
Lemma lem3260172 {_85450 : Type'} (GEN_PVAR_15 : _85450) (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term21 _85450 GEN_PVAR_15 s t P x) = (term22 _85450 GEN_PVAR_15 s t P x).
Proof. exact (MK_COMB (@lem3260171 _85450 GEN_PVAR_15) (@lem3260170 _85450 s t P x)). Qed.
Lemma lem3260173 {_85450 : Type'} (x : _85450) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3260174 {_85450 : Type'} (GEN_PVAR_15 : _85450) (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term23 _85450 GEN_PVAR_15 s t P x) = (term24 _85450 GEN_PVAR_15 s t P x).
Proof. exact (MK_COMB (@lem3260172 _85450 GEN_PVAR_15 s t P x) (@lem3260173 _85450 x)). Qed.
Lemma lem3260175 {_85450 : Type'} (GEN_PVAR_15 : _85450) (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) : (term25 _85450 GEN_PVAR_15 s t P) = (term26 _85450 GEN_PVAR_15 s t P).
Proof. exact (fun_ext (fun x : _85450 => @lem3260174 _85450 GEN_PVAR_15 s t P x)). Qed.
Lemma lem3260176 {_85450 : Type'} : (@ex _85450) = (@ex _85450).
Proof. exact (eq_refl (@ex _85450)). Qed.
Lemma lem3260177 {_85450 : Type'} (GEN_PVAR_15 : _85450) (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) : (term27 _85450 GEN_PVAR_15 s t P) = (term28 _85450 GEN_PVAR_15 s t P).
Proof. exact (MK_COMB (@lem3260176 _85450) (@lem3260175 _85450 GEN_PVAR_15 s t P)). Qed.
Lemma lem3260178 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) : (term29 _85450 s t P) = (term30 _85450 s t P).
Proof. exact (fun_ext (fun GEN_PVAR_15 : _85450 => @lem3260177 _85450 GEN_PVAR_15 s t P)). Qed.
Lemma lem3260179 {_85450 : Type'} : (@GSPEC _85450) = (@GSPEC _85450).
Proof. exact (eq_refl (@GSPEC _85450)). Qed.
Lemma lem3260180 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) : (term31 _85450 s t P) = (term1 _85450 s t P).
Proof. exact (MK_COMB (@lem3260179 _85450) (@lem3260178 _85450 s t P)). Qed.
Lemma lem3260181 {_85450 : Type'} (x : _85450) : (@IN _85450 x) = (@IN _85450 x).
Proof. exact (eq_refl (@IN _85450 x)). Qed.
Lemma lem3260182 {_85450 : Type'} (x : _85450) (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) : (term17 _85450 x s t P) = (term32 _85450 x s t P).
Proof. exact (MK_COMB (@lem3260181 _85450 x) (@lem3260180 _85450 s t P)). Qed.
Lemma lem3260183 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3260184 {_85450 : Type'} (x : _85450) (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) : (term33 _85450 x s t P) = (term34 _85450 x s t P).
Proof. exact (MK_COMB (@lem3260183) (@lem3260182 _85450 x s t P)). Qed.
Lemma lem3260185 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term18 _85450 s t P x) = (term20 _85450 s t P x).
Proof. exact (eq_refl (term18 _85450 s t P x)). Qed.
Lemma lem3260186 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : ((term17 _85450 x s t P) = (term18 _85450 s t P x)) = ((term32 _85450 x s t P) = (term20 _85450 s t P x)).
Proof. exact (MK_COMB (@lem3260184 _85450 x s t P) (@lem3260185 _85450 s t P x)). Qed.
Lemma lem3260187 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term32 _85450 x s t P) = (term20 _85450 s t P x).
Proof. exact (EQ_MP (@lem3260186 _85450 s t P x) (@lem3260169 _85450 s t P x)). Qed.
Lemma lem3260191 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term35 A x s t) = (term36 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3260192 {_85450 : Type'} (s : _85450 -> Prop) (x : _85450) (t : _85450 -> Prop) : (term35 _85450 x s t) = (term36 _85450 s x t).
Proof. exact (@lem3260191 _85450 s x t). Qed.
Lemma lem3260196 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3260197 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) : (@IN _85450 x P) = (P x).
Proof. exact (@lem3260196 _85450 P x). Qed.
Lemma lem3260198 {_85450 : Type'} (s : _85450 -> Prop) (x : _85450) : (@IN _85450 x s) = (s x).
Proof. exact (@lem3260197 _85450 s x). Qed.
Lemma lem3260199 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3260200 {_85450 : Type'} (s : _85450 -> Prop) (x : _85450) : (term37 _85450 x s) = (term38 _85450 s x).
Proof. exact (MK_COMB (@lem3260199) (@lem3260198 _85450 s x)). Qed.
Lemma lem3260202 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3260203 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) : (@IN _85450 x P) = (P x).
Proof. exact (@lem3260202 _85450 P x). Qed.
Lemma lem3260204 {_85450 : Type'} (t : _85450 -> Prop) (x : _85450) : (@IN _85450 x t) = (t x).
Proof. exact (@lem3260203 _85450 t x). Qed.
Lemma lem3260205 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (x : _85450) : (term36 _85450 s x t) = (term39 _85450 s t x).
Proof. exact (MK_COMB (@lem3260200 _85450 s x) (@lem3260204 _85450 t x)). Qed.
Lemma lem3260208 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (x : _85450) : (term35 _85450 x s t) = (term39 _85450 s t x).
Proof. exact (TRANS (@lem3260192 _85450 s x t) (@lem3260205 _85450 s t x)). Qed.
Lemma lem3260209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3260210 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (x : _85450) : (term40 _85450 x s t) = (term41 _85450 s t x).
Proof. exact (MK_COMB (@lem3260209) (@lem3260208 _85450 s t x)). Qed.
Lemma lem3260211 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3260212 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term20 _85450 s t P x) = (term42 _85450 s t P x).
Proof. exact (MK_COMB (@lem3260210 _85450 s t x) (@lem3260211 _85450 P x)). Qed.
Lemma lem3260215 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term32 _85450 x s t P) = (term42 _85450 s t P x).
Proof. exact (TRANS (@lem3260187 _85450 s t P x) (@lem3260212 _85450 s t P x)). Qed.
Lemma lem3260216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3260217 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term34 _85450 x s t P) = (term43 _85450 s t P x).
Proof. exact (MK_COMB (@lem3260216) (@lem3260215 _85450 s t P x)). Qed.
Lemma lem3260219 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term35 A x s t) = (term36 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3260220 {_85450 : Type'} (s : _85450 -> Prop) (x : _85450) (t : _85450 -> Prop) : (term35 _85450 x s t) = (term36 _85450 s x t).
Proof. exact (@lem3260219 _85450 s x t). Qed.
Lemma lem3260221 {_85450 : Type'} (s : _85450 -> Prop) (x : _85450) (t : _85450 -> Prop) (P : _85450 -> Prop) : (term44 _85450 x s t P) = (term45 _85450 s x t P).
Proof. exact (@lem3260220 _85450 (term46 _85450 s P) x (term46 _85450 t P)). Qed.
Lemma lem3260225 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term16 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3260226 {_85450 : Type'} (p : _85450 -> Prop) (x : _85450) : (term16 _85450 x p) = (p x).
Proof. exact (@lem3260225 _85450 p x). Qed.
Lemma lem3260227 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term47 _85450 x s P) = (term48 _85450 s P x).
Proof. exact (@lem3260226 _85450 (term49 _85450 s P) x). Qed.
Lemma lem3260228 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term48 _85450 s P x) = (term50 _85450 s P x).
Proof. exact (eq_refl (term48 _85450 s P x)). Qed.
Lemma lem3260229 {_85450 : Type'} (GEN_PVAR_16 : _85450) : (@SETSPEC _85450 GEN_PVAR_16) = (@SETSPEC _85450 GEN_PVAR_16).
Proof. exact (eq_refl (@SETSPEC _85450 GEN_PVAR_16)). Qed.
Lemma lem3260230 {_85450 : Type'} (GEN_PVAR_16 : _85450) (s : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term51 _85450 GEN_PVAR_16 s P x) = (term52 _85450 GEN_PVAR_16 s P x).
Proof. exact (MK_COMB (@lem3260229 _85450 GEN_PVAR_16) (@lem3260228 _85450 s P x)). Qed.
Lemma lem3260231 {_85450 : Type'} (x : _85450) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3260232 {_85450 : Type'} (GEN_PVAR_16 : _85450) (s : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term53 _85450 GEN_PVAR_16 s P x) = (term54 _85450 GEN_PVAR_16 s P x).
Proof. exact (MK_COMB (@lem3260230 _85450 GEN_PVAR_16 s P x) (@lem3260231 _85450 x)). Qed.
Lemma lem3260233 {_85450 : Type'} (GEN_PVAR_16 : _85450) (s : _85450 -> Prop) (P : _85450 -> Prop) : (term55 _85450 GEN_PVAR_16 s P) = (term56 _85450 GEN_PVAR_16 s P).
Proof. exact (fun_ext (fun x : _85450 => @lem3260232 _85450 GEN_PVAR_16 s P x)). Qed.
Lemma lem3260234 {_85450 : Type'} : (@ex _85450) = (@ex _85450).
Proof. exact (eq_refl (@ex _85450)). Qed.
Lemma lem3260235 {_85450 : Type'} (GEN_PVAR_16 : _85450) (s : _85450 -> Prop) (P : _85450 -> Prop) : (term57 _85450 GEN_PVAR_16 s P) = (term58 _85450 GEN_PVAR_16 s P).
Proof. exact (MK_COMB (@lem3260234 _85450) (@lem3260233 _85450 GEN_PVAR_16 s P)). Qed.
Lemma lem3260236 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) : (term59 _85450 s P) = (term60 _85450 s P).
Proof. exact (fun_ext (fun GEN_PVAR_16 : _85450 => @lem3260235 _85450 GEN_PVAR_16 s P)). Qed.
Lemma lem3260237 {_85450 : Type'} : (@GSPEC _85450) = (@GSPEC _85450).
Proof. exact (eq_refl (@GSPEC _85450)). Qed.
Lemma lem3260238 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) : (term61 _85450 s P) = (term46 _85450 s P).
Proof. exact (MK_COMB (@lem3260237 _85450) (@lem3260236 _85450 s P)). Qed.
Lemma lem3260239 {_85450 : Type'} (x : _85450) : (@IN _85450 x) = (@IN _85450 x).
Proof. exact (eq_refl (@IN _85450 x)). Qed.
Lemma lem3260240 {_85450 : Type'} (x : _85450) (s : _85450 -> Prop) (P : _85450 -> Prop) : (term47 _85450 x s P) = (term62 _85450 x s P).
Proof. exact (MK_COMB (@lem3260239 _85450 x) (@lem3260238 _85450 s P)). Qed.
Lemma lem3260241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3260242 {_85450 : Type'} (x : _85450) (s : _85450 -> Prop) (P : _85450 -> Prop) : (term63 _85450 x s P) = (term64 _85450 x s P).
Proof. exact (MK_COMB (@lem3260241) (@lem3260240 _85450 x s P)). Qed.
Lemma lem3260243 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term48 _85450 s P x) = (term50 _85450 s P x).
Proof. exact (eq_refl (term48 _85450 s P x)). Qed.
Lemma lem3260244 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : ((term47 _85450 x s P) = (term48 _85450 s P x)) = ((term62 _85450 x s P) = (term50 _85450 s P x)).
Proof. exact (MK_COMB (@lem3260242 _85450 x s P) (@lem3260243 _85450 s P x)). Qed.
Lemma lem3260245 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term62 _85450 x s P) = (term50 _85450 s P x).
Proof. exact (EQ_MP (@lem3260244 _85450 s P x) (@lem3260227 _85450 s P x)). Qed.
Lemma lem3260249 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3260250 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) : (@IN _85450 x P) = (P x).
Proof. exact (@lem3260249 _85450 P x). Qed.
Lemma lem3260251 {_85450 : Type'} (s : _85450 -> Prop) (x : _85450) : (@IN _85450 x s) = (s x).
Proof. exact (@lem3260250 _85450 s x). Qed.
Lemma lem3260252 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3260253 {_85450 : Type'} (s : _85450 -> Prop) (x : _85450) : (term37 _85450 x s) = (term38 _85450 s x).
Proof. exact (MK_COMB (@lem3260252) (@lem3260251 _85450 s x)). Qed.
Lemma lem3260254 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3260255 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term50 _85450 s P x) = (term39 _85450 s P x).
Proof. exact (MK_COMB (@lem3260253 _85450 s x) (@lem3260254 _85450 P x)). Qed.
Lemma lem3260258 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term62 _85450 x s P) = (term39 _85450 s P x).
Proof. exact (TRANS (@lem3260245 _85450 s P x) (@lem3260255 _85450 s P x)). Qed.
Lemma lem3260259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3260260 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term65 _85450 x s P) = (term41 _85450 s P x).
Proof. exact (MK_COMB (@lem3260259) (@lem3260258 _85450 s P x)). Qed.
Lemma lem3260262 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term16 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3260263 {_85450 : Type'} (p : _85450 -> Prop) (x : _85450) : (term16 _85450 x p) = (p x).
Proof. exact (@lem3260262 _85450 p x). Qed.
Lemma lem3260264 {_85450 : Type'} (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term47 _85450 x t P) = (term48 _85450 t P x).
Proof. exact (@lem3260263 _85450 (term49 _85450 t P) x). Qed.
Lemma lem3260265 {_85450 : Type'} (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term48 _85450 t P x) = (term50 _85450 t P x).
Proof. exact (eq_refl (term48 _85450 t P x)). Qed.
Lemma lem3260266 {_85450 : Type'} (GEN_PVAR_17 : _85450) : (@SETSPEC _85450 GEN_PVAR_17) = (@SETSPEC _85450 GEN_PVAR_17).
Proof. exact (eq_refl (@SETSPEC _85450 GEN_PVAR_17)). Qed.
Lemma lem3260267 {_85450 : Type'} (GEN_PVAR_17 : _85450) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term51 _85450 GEN_PVAR_17 t P x) = (term52 _85450 GEN_PVAR_17 t P x).
Proof. exact (MK_COMB (@lem3260266 _85450 GEN_PVAR_17) (@lem3260265 _85450 t P x)). Qed.
Lemma lem3260268 {_85450 : Type'} (x : _85450) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3260269 {_85450 : Type'} (GEN_PVAR_17 : _85450) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term53 _85450 GEN_PVAR_17 t P x) = (term54 _85450 GEN_PVAR_17 t P x).
Proof. exact (MK_COMB (@lem3260267 _85450 GEN_PVAR_17 t P x) (@lem3260268 _85450 x)). Qed.
Lemma lem3260270 {_85450 : Type'} (GEN_PVAR_17 : _85450) (t : _85450 -> Prop) (P : _85450 -> Prop) : (term55 _85450 GEN_PVAR_17 t P) = (term56 _85450 GEN_PVAR_17 t P).
Proof. exact (fun_ext (fun x : _85450 => @lem3260269 _85450 GEN_PVAR_17 t P x)). Qed.
Lemma lem3260271 {_85450 : Type'} : (@ex _85450) = (@ex _85450).
Proof. exact (eq_refl (@ex _85450)). Qed.
Lemma lem3260272 {_85450 : Type'} (GEN_PVAR_17 : _85450) (t : _85450 -> Prop) (P : _85450 -> Prop) : (term57 _85450 GEN_PVAR_17 t P) = (term58 _85450 GEN_PVAR_17 t P).
Proof. exact (MK_COMB (@lem3260271 _85450) (@lem3260270 _85450 GEN_PVAR_17 t P)). Qed.
Lemma lem3260273 {_85450 : Type'} (t : _85450 -> Prop) (P : _85450 -> Prop) : (term59 _85450 t P) = (term60 _85450 t P).
Proof. exact (fun_ext (fun GEN_PVAR_17 : _85450 => @lem3260272 _85450 GEN_PVAR_17 t P)). Qed.
Lemma lem3260274 {_85450 : Type'} : (@GSPEC _85450) = (@GSPEC _85450).
Proof. exact (eq_refl (@GSPEC _85450)). Qed.
Lemma lem3260275 {_85450 : Type'} (t : _85450 -> Prop) (P : _85450 -> Prop) : (term61 _85450 t P) = (term46 _85450 t P).
Proof. exact (MK_COMB (@lem3260274 _85450) (@lem3260273 _85450 t P)). Qed.
Lemma lem3260276 {_85450 : Type'} (x : _85450) : (@IN _85450 x) = (@IN _85450 x).
Proof. exact (eq_refl (@IN _85450 x)). Qed.
Lemma lem3260277 {_85450 : Type'} (x : _85450) (t : _85450 -> Prop) (P : _85450 -> Prop) : (term47 _85450 x t P) = (term62 _85450 x t P).
Proof. exact (MK_COMB (@lem3260276 _85450 x) (@lem3260275 _85450 t P)). Qed.
Lemma lem3260278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3260279 {_85450 : Type'} (x : _85450) (t : _85450 -> Prop) (P : _85450 -> Prop) : (term63 _85450 x t P) = (term64 _85450 x t P).
Proof. exact (MK_COMB (@lem3260278) (@lem3260277 _85450 x t P)). Qed.
Lemma lem3260280 {_85450 : Type'} (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term48 _85450 t P x) = (term50 _85450 t P x).
Proof. exact (eq_refl (term48 _85450 t P x)). Qed.
Lemma lem3260281 {_85450 : Type'} (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : ((term47 _85450 x t P) = (term48 _85450 t P x)) = ((term62 _85450 x t P) = (term50 _85450 t P x)).
Proof. exact (MK_COMB (@lem3260279 _85450 x t P) (@lem3260280 _85450 t P x)). Qed.
Lemma lem3260282 {_85450 : Type'} (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term62 _85450 x t P) = (term50 _85450 t P x).
Proof. exact (EQ_MP (@lem3260281 _85450 t P x) (@lem3260264 _85450 t P x)). Qed.
Lemma lem3260286 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3260287 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) : (@IN _85450 x P) = (P x).
Proof. exact (@lem3260286 _85450 P x). Qed.
Lemma lem3260288 {_85450 : Type'} (t : _85450 -> Prop) (x : _85450) : (@IN _85450 x t) = (t x).
Proof. exact (@lem3260287 _85450 t x). Qed.
Lemma lem3260289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3260290 {_85450 : Type'} (t : _85450 -> Prop) (x : _85450) : (term37 _85450 x t) = (term38 _85450 t x).
Proof. exact (MK_COMB (@lem3260289) (@lem3260288 _85450 t x)). Qed.
Lemma lem3260291 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3260292 {_85450 : Type'} (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term50 _85450 t P x) = (term39 _85450 t P x).
Proof. exact (MK_COMB (@lem3260290 _85450 t x) (@lem3260291 _85450 P x)). Qed.
Lemma lem3260295 {_85450 : Type'} (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term62 _85450 x t P) = (term39 _85450 t P x).
Proof. exact (TRANS (@lem3260282 _85450 t P x) (@lem3260292 _85450 t P x)). Qed.
Lemma lem3260296 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term45 _85450 s x t P) = (term66 _85450 s t P x).
Proof. exact (MK_COMB (@lem3260260 _85450 s P x) (@lem3260295 _85450 t P x)). Qed.
Lemma lem3260299 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term44 _85450 x s t P) = (term66 _85450 s t P x).
Proof. exact (TRANS (@lem3260221 _85450 s x t P) (@lem3260296 _85450 s t P x)). Qed.
Lemma lem3260300 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : ((term32 _85450 x s t P) = (term44 _85450 x s t P)) = ((term42 _85450 s t P x) = (term66 _85450 s t P x)).
Proof. exact (MK_COMB (@lem3260217 _85450 s t P x) (@lem3260299 _85450 s t P x)). Qed.
Lemma lem3260303 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) : (term67 _85450 s t P) = (term68 _85450 s t P).
Proof. exact (fun_ext (fun x : _85450 => @lem3260300 _85450 s t P x)). Qed.
Lemma lem3260304 {_85450 : Type'} : (@all _85450) = (@all _85450).
Proof. exact (eq_refl (@all _85450)). Qed.
Lemma lem3260305 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) : (term3 _85450 s t P) = (term69 _85450 s t P).
Proof. exact (MK_COMB (@lem3260304 _85450) (@lem3260303 _85450 s t P)). Qed.
Lemma lem3260310 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) : (term5 _85450 s P) = (term70 _85450 s P).
Proof. exact (fun_ext (fun t : _85450 -> Prop => @lem3260305 _85450 s t P)). Qed.
Lemma lem3260311 {_85450 : Type'} : (@all (_85450 -> Prop)) = (@all (_85450 -> Prop)).
Proof. exact (eq_refl (@all (_85450 -> Prop))). Qed.
Lemma lem3260312 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) : (term7 _85450 s P) = (term71 _85450 s P).
Proof. exact (MK_COMB (@lem3260311 _85450) (@lem3260310 _85450 s P)). Qed.
Lemma lem3260317 {_85450 : Type'} (P : _85450 -> Prop) : (term9 _85450 P) = (term72 _85450 P).
Proof. exact (fun_ext (fun s : _85450 -> Prop => @lem3260312 _85450 s P)). Qed.
Lemma lem3260318 {_85450 : Type'} : (@all (_85450 -> Prop)) = (@all (_85450 -> Prop)).
Proof. exact (eq_refl (@all (_85450 -> Prop))). Qed.
Lemma lem3260319 {_85450 : Type'} (P : _85450 -> Prop) : (term11 _85450 P) = (term73 _85450 P).
Proof. exact (MK_COMB (@lem3260318 _85450) (@lem3260317 _85450 P)). Qed.
Lemma lem3260324 {_85450 : Type'} : (term13 _85450) = (term74 _85450).
Proof. exact (fun_ext (fun P : _85450 -> Prop => @lem3260319 _85450 P)). Qed.
Lemma lem3260325 {_85450 : Type'} : (@all (_85450 -> Prop)) = (@all (_85450 -> Prop)).
Proof. exact (eq_refl (@all (_85450 -> Prop))). Qed.
Lemma lem3260326 {_85450 : Type'} : (term15 _85450) = (term75 _85450).
Proof. exact (MK_COMB (@lem3260325 _85450) (@lem3260324 _85450)). Qed.
Lemma lem3260331 {_85450 : Type'} : (term75 _85450) = (term15 _85450).
Proof. exact (SYM (@lem3260326 _85450)). Qed.
Lemma lem3260333 (p : Prop) : p = (term76 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3260334 {_85450 : Type'} : (term75 _85450) = (term77 _85450).
Proof. exact (@lem3260333 (term75 _85450)). Qed.
Lemma lem3260335 {_85450 : Type'} : (term77 _85450) = (term75 _85450).
Proof. exact (SYM (@lem3260334 _85450)). Qed.
Lemma lem3260336 {_85450 : Type'} (h1 : term78 _85450) : term78 _85450.
Proof. exact (h1). Qed.
Lemma lem3260339 {_85450 : Type'} (h1 : term77 _85450) : term77 _85450.
Proof. exact (h1). Qed.
Lemma lem3260340 {_85450 : Type'} : term79 _85450.
Proof. exact (fun h0 : term77 _85450 => @lem3260339 _85450 h0). Qed.
Lemma lem3260341 {_85450 : Type'} (h1 : term79 _85450) : term79 _85450.
Proof. exact (h1). Qed.
Lemma lem3260342 {_85450 : Type'} (h1 : term77 _85450) : term77 _85450.
Proof. exact (h1). Qed.
Lemma lem3260343 {_85450 : Type'} (h1 : term77 _85450) (h2 : term79 _85450) : term77 _85450.
Proof. exact (@lem3260341 _85450 h2 (@lem3260342 _85450 h1)). Qed.
Lemma lem3260344 {_85450 : Type'} (h1 : term77 _85450) : term80 _85450.
Proof. exact (fun h0 : term79 _85450 => @lem3260343 _85450 h1 h0). Qed.
Lemma lem3260345 {_85450 : Type'} (h1 : term79 _85450) : term79 _85450.
Proof. exact (h1). Qed.
Lemma lem3260346 {_85450 : Type'} (h1 : term77 _85450) (h2 : term79 _85450) : term77 _85450.
Proof. exact (@lem3260344 _85450 h1 (@lem3260345 _85450 h2)). Qed.
Lemma lem3260347 {_85450 : Type'} (h1 : term79 _85450) : term79 _85450.
Proof. exact (fun h0 : term77 _85450 => @lem3260346 _85450 h0 h1). Qed.
Lemma lem3260348 {_85450 : Type'} : term81 _85450.
Proof. exact (fun h0 : term79 _85450 => @lem3260347 _85450 h0). Qed.
Lemma lem3260351 {_85450 : Type'} : term79 _85450.
Proof. exact (@lem3260348 _85450 (@lem3260340 _85450)). Qed.
Lemma lem3260352 {_85450 : Type'} : term79 _85450.
Proof. exact (@lem3260351 _85450). Qed.
Lemma lem3260354 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3260355 {_85450 : Type'} : (term77 _85450) = (term82 _85450).
Proof. exact (@lem3260354 (term78 _85450)). Qed.
Lemma lem3260357 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3260358 {_85450 : Type'} : (term82 _85450) = (term75 _85450).
Proof. exact (@lem3260357 (term75 _85450)). Qed.
Lemma lem3260389 {_85450 : Type'} : (term77 _85450) = (term75 _85450).
Proof. exact (TRANS (@lem3260355 _85450) (@lem3260358 _85450)). Qed.
Lemma lem3260414 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : ((term42 _85450 s t P x) = (term66 _85450 s t P x)) = ((term42 _85450 s t P x) = (term66 _85450 s t P x)).
Proof. exact (eq_refl ((term42 _85450 s t P x) = (term66 _85450 s t P x))). Qed.
Lemma lem3260415 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) : (term68 _85450 s t P) = (term68 _85450 s t P).
Proof. exact (fun_ext (fun x : _85450 => @lem3260414 _85450 s t P x)). Qed.
Lemma lem3260416 {_85450 : Type'} : (@all _85450) = (@all _85450).
Proof. exact (eq_refl (@all _85450)). Qed.
Lemma lem3260417 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) : (term69 _85450 s t P) = (term69 _85450 s t P).
Proof. exact (MK_COMB (@lem3260416 _85450) (@lem3260415 _85450 s t P)). Qed.
Lemma lem3260418 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) : (term70 _85450 s P) = (term70 _85450 s P).
Proof. exact (fun_ext (fun t : _85450 -> Prop => @lem3260417 _85450 s t P)). Qed.
Lemma lem3260419 {_85450 : Type'} : (@all (_85450 -> Prop)) = (@all (_85450 -> Prop)).
Proof. exact (eq_refl (@all (_85450 -> Prop))). Qed.
Lemma lem3260420 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) : (term71 _85450 s P) = (term71 _85450 s P).
Proof. exact (MK_COMB (@lem3260419 _85450) (@lem3260418 _85450 s P)). Qed.
Lemma lem3260421 {_85450 : Type'} (P : _85450 -> Prop) : (term72 _85450 P) = (term72 _85450 P).
Proof. exact (fun_ext (fun s : _85450 -> Prop => @lem3260420 _85450 s P)). Qed.
Lemma lem3260422 {_85450 : Type'} : (@all (_85450 -> Prop)) = (@all (_85450 -> Prop)).
Proof. exact (eq_refl (@all (_85450 -> Prop))). Qed.
Lemma lem3260423 {_85450 : Type'} (P : _85450 -> Prop) : (term73 _85450 P) = (term73 _85450 P).
Proof. exact (MK_COMB (@lem3260422 _85450) (@lem3260421 _85450 P)). Qed.
Lemma lem3260424 {_85450 : Type'} : (term74 _85450) = (term74 _85450).
Proof. exact (fun_ext (fun P : _85450 -> Prop => @lem3260423 _85450 P)). Qed.
Lemma lem3260425 {_85450 : Type'} : (@all (_85450 -> Prop)) = (@all (_85450 -> Prop)).
Proof. exact (eq_refl (@all (_85450 -> Prop))). Qed.
Lemma lem3260426 {_85450 : Type'} : (term75 _85450) = (term75 _85450).
Proof. exact (MK_COMB (@lem3260425 _85450) (@lem3260424 _85450)). Qed.
Lemma lem3260463 {_85450 : Type'} : (term77 _85450) = (term75 _85450).
Proof. exact (TRANS (@lem3260389 _85450) (@lem3260426 _85450)). Qed.
Lemma lem3260464 {_85450 : Type'} : (term75 _85450) = (term77 _85450).
Proof. exact (SYM (@lem3260463 _85450)). Qed.
Lemma lem3260466 (p : Prop) : p = (term76 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3260467 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : ((term42 _85450 s t P x) = (term66 _85450 s t P x)) = (term84 _85450 s t P x).
Proof. exact (@lem3260466 ((term42 _85450 s t P x) = (term66 _85450 s t P x))). Qed.
Lemma lem3260468 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term84 _85450 s t P x) = ((term42 _85450 s t P x) = (term66 _85450 s t P x)).
Proof. exact (SYM (@lem3260467 _85450 s t P x)). Qed.
Lemma lem3260469 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term85 _85450 s t P x) : term85 _85450 s t P x.
Proof. exact (h1). Qed.
Lemma lem3260478 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (x : _85450) : (term86 _85450 s t x) = (term87 _85450 s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem3260482 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) : (term88 _85450 P x) = (term88 _85450 P x).
Proof. exact (eq_refl (term88 _85450 P x)). Qed.
Lemma lem3260484 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3260485 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (x : _85450) : (term89 _85450 s t x) = (term90 _85450 s t x).
Proof. exact (MK_COMB (@lem3260484) (@lem3260478 _85450 s t x)). Qed.
Lemma lem3260486 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term91 _85450 s t P x) = (term92 _85450 s t P x).
Proof. exact (MK_COMB (@lem3260485 _85450 s t x) (@lem3260482 _85450 P x)). Qed.
Lemma lem3260487 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term93 _85450 s t P x) = (term91 _85450 s t P x).
Proof. exact (@lem17045 (term39 _85450 s t x) (P x)). Qed.
Lemma lem3260488 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term93 _85450 s t P x) = (term92 _85450 s t P x).
Proof. exact (TRANS (@lem3260487 _85450 s t P x) (@lem3260486 _85450 s t P x)). Qed.
Lemma lem3260500 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term86 _85450 s P x) = (term87 _85450 s P x).
Proof. exact (@lem17045 (s x) (P x)). Qed.
Lemma lem3260512 {_85450 : Type'} (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term86 _85450 t P x) = (term87 _85450 t P x).
Proof. exact (@lem17045 (t x) (P x)). Qed.
Lemma lem3260516 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3260517 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term89 _85450 s P x) = (term90 _85450 s P x).
Proof. exact (MK_COMB (@lem3260516) (@lem3260500 _85450 s P x)). Qed.
Lemma lem3260518 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term94 _85450 s t P x) = (term95 _85450 s t P x).
Proof. exact (MK_COMB (@lem3260517 _85450 s P x) (@lem3260512 _85450 t P x)). Qed.
Lemma lem3260519 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term96 _85450 s t P x) = (term94 _85450 s t P x).
Proof. exact (@lem17045 (term39 _85450 s P x) (term39 _85450 t P x)). Qed.
Lemma lem3260520 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term96 _85450 s t P x) = (term95 _85450 s t P x).
Proof. exact (TRANS (@lem3260519 _85450 s t P x) (@lem3260518 _85450 s t P x)). Qed.
Lemma lem3260523 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term66 _85450 s t P x) = (term66 _85450 s t P x).
Proof. exact (eq_refl (term66 _85450 s t P x)). Qed.
Lemma lem3260524 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3260525 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term97 _85450 s t P x) = (term98 _85450 s t P x).
Proof. exact (MK_COMB (@lem3260524) (@lem3260488 _85450 s t P x)). Qed.
Lemma lem3260526 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term99 _85450 s t P x) = (term100 _85450 s t P x).
Proof. exact (MK_COMB (@lem3260525 _85450 s t P x) (@lem3260523 _85450 s t P x)). Qed.
Lemma lem3260528 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term101 _85450 s t P x) = (term101 _85450 s t P x).
Proof. exact (eq_refl (term101 _85450 s t P x)). Qed.
Lemma lem3260529 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term102 _85450 s t P x) = (term103 _85450 s t P x).
Proof. exact (MK_COMB (@lem3260528 _85450 s t P x) (@lem3260520 _85450 s t P x)). Qed.
Lemma lem3260530 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3260531 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term104 _85450 s t P x) = (term105 _85450 s t P x).
Proof. exact (MK_COMB (@lem3260530) (@lem3260529 _85450 s t P x)). Qed.
Lemma lem3260532 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term106 _85450 s t P x) = (term107 _85450 s t P x).
Proof. exact (MK_COMB (@lem3260531 _85450 s t P x) (@lem3260526 _85450 s t P x)). Qed.
Lemma lem3260533 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term85 _85450 s t P x) = (term106 _85450 s t P x).
Proof. exact (@lem17646 (term42 _85450 s t P x) (term66 _85450 s t P x)). Qed.
Lemma lem3260538 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term85 _85450 s t P x) = (term107 _85450 s t P x).
Proof. exact (TRANS (@lem3260533 _85450 s t P x) (@lem3260532 _85450 s t P x)). Qed.
Lemma lem3260635 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term85 _85450 s t P x) : term107 _85450 s t P x.
Proof. exact (EQ_MP (@lem3260538 _85450 s t P x) (@lem3260469 _85450 s t P x h1)). Qed.
Lemma lem3260636 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) : term103 _85450 s t P x.
Proof. exact (h1). Qed.
Lemma lem3260637 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term100 _85450 s t P x) : term100 _85450 s t P x.
Proof. exact (h1). Qed.
Lemma lem3260638 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) : term95 _85450 s t P x.
Proof. exact (proj2 (@lem3260636 _85450 s t P x h1)). Qed.
Lemma lem3260639 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) : term42 _85450 s t P x.
Proof. exact (proj1 (@lem3260636 _85450 s t P x h1)). Qed.
Lemma lem3260641 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) : term39 _85450 s t x.
Proof. exact (proj1 (@lem3260639 _85450 s t P x h1)). Qed.
Lemma lem3260644 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term87 _85450 s P x) : term87 _85450 s P x.
Proof. exact (h1). Qed.
Lemma lem3260645 {_85450 : Type'} (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term87 _85450 t P x) : term87 _85450 t P x.
Proof. exact (h1). Qed.
Lemma lem3260650 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term100 _85450 s t P x) : term66 _85450 s t P x.
Proof. exact (proj2 (@lem3260637 _85450 s t P x h1)). Qed.
Lemma lem3260651 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term100 _85450 s t P x) : term92 _85450 s t P x.
Proof. exact (proj1 (@lem3260637 _85450 s t P x h1)). Qed.
Lemma lem3260652 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term100 _85450 s t P x) : term39 _85450 t P x.
Proof. exact (proj2 (@lem3260650 _85450 s t P x h1)). Qed.
Lemma lem3260653 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term100 _85450 s t P x) : term39 _85450 s P x.
Proof. exact (proj1 (@lem3260650 _85450 s t P x h1)). Qed.
Lemma lem3260658 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (x : _85450) (h1 : term87 _85450 s t x) : term87 _85450 s t x.
Proof. exact (h1). Qed.
Lemma lem3260677 {_85450 : Type'} (s : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) : term88 _85450 s x.
Proof. exact (h1). Qed.
Lemma lem3260693 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) : term88 _85450 P x.
Proof. exact (h1). Qed.
Lemma lem3260709 {_85450 : Type'} (t : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) : term88 _85450 t x.
Proof. exact (h1). Qed.
Lemma lem3260725 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) : term88 _85450 P x.
Proof. exact (h1). Qed.
Lemma lem3260745 {_85450 : Type'} (s : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) : term88 _85450 s x.
Proof. exact (h1). Qed.
Lemma lem3260765 {_85450 : Type'} (t : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) : term88 _85450 t x.
Proof. exact (h1). Qed.
Lemma lem3260785 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) : term88 _85450 P x.
Proof. exact (h1). Qed.
Lemma lem3260793 {_85450 : Type'} (s : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) : term88 _85450 s x.
Proof. exact (h1). Qed.
Lemma lem3260801 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) : term88 _85450 P x.
Proof. exact (h1). Qed.
Lemma lem3260809 {_85450 : Type'} (t : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) : term88 _85450 t x.
Proof. exact (h1). Qed.
Lemma lem3260817 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) : term88 _85450 P x.
Proof. exact (h1). Qed.
Lemma lem3260827 {_85450 : Type'} (s : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) : term88 _85450 s x.
Proof. exact (h1). Qed.
Lemma lem3260837 {_85450 : Type'} (t : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) : term88 _85450 t x.
Proof. exact (h1). Qed.
Lemma lem3260847 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) : term88 _85450 P x.
Proof. exact (h1). Qed.
Lemma lem3260849 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) : s x.
Proof. exact (proj1 (@lem3260641 _85450 s t P x h1)). Qed.
Lemma lem3260850 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) : term108 _85450 s x.
Proof. exact (fun h0 : term88 _85450 s x => @lem3260849 _85450 s t P x h1). Qed.
Lemma lem3260852 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3260853 {_85450 : Type'} (s : _85450 -> Prop) (x : _85450) : (term108 _85450 s x) = (s x).
Proof. exact (@lem3260852 (s x)). Qed.
Lemma lem3260854 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) : s x.
Proof. exact (EQ_MP (@lem3260853 _85450 s x) (@lem3260850 _85450 s t P x h1)). Qed.
Lemma lem3260857 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3260859 {_85450 : Type'} (s : _85450 -> Prop) (x : _85450) : (term88 _85450 s x) = (term110 _85450 s x).
Proof. exact (@lem3260857 (s x)). Qed.
Lemma lem3260862 {_85450 : Type'} (s : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) : term110 _85450 s x.
Proof. exact (EQ_MP (@lem3260859 _85450 s x) (@lem3260793 _85450 s x h1)). Qed.
Lemma lem3260865 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (@lem3260862 _85450 s x h1 (@lem3260854 _85450 s t P x h2)). Qed.
Lemma lem3260866 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term103 _85450 s t P x) : term111.
Proof. exact (fun h0 : ~ False => @lem3260865 _85450 s t P x h1 h2). Qed.
Lemma lem3260868 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3260869 : term111 = False.
Proof. exact (@lem3260868 False). Qed.
Lemma lem3260870 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3260869) (@lem3260866 _85450 s t P x h1 h2)). Qed.
Lemma lem3260872 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) : P x.
Proof. exact (proj2 (@lem3260639 _85450 s t P x h1)). Qed.
Lemma lem3260873 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) : term108 _85450 P x.
Proof. exact (fun h0 : term88 _85450 P x => @lem3260872 _85450 s t P x h1). Qed.
Lemma lem3260875 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3260876 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) : (term108 _85450 P x) = (P x).
Proof. exact (@lem3260875 (P x)). Qed.
Lemma lem3260877 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) : P x.
Proof. exact (EQ_MP (@lem3260876 _85450 P x) (@lem3260873 _85450 s t P x h1)). Qed.
Lemma lem3260880 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3260882 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) : (term88 _85450 P x) = (term110 _85450 P x).
Proof. exact (@lem3260880 (P x)). Qed.
Lemma lem3260885 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) : term110 _85450 P x.
Proof. exact (EQ_MP (@lem3260882 _85450 P x) (@lem3260801 _85450 P x h1)). Qed.
Lemma lem3260888 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (@lem3260885 _85450 P x h1 (@lem3260877 _85450 s t P x h2)). Qed.
Lemma lem3260889 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : term111.
Proof. exact (fun h0 : ~ False => @lem3260888 _85450 s t P x h1 h2). Qed.
Lemma lem3260891 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3260892 : term111 = False.
Proof. exact (@lem3260891 False). Qed.
Lemma lem3260893 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3260892) (@lem3260889 _85450 s t P x h1 h2)). Qed.
Lemma lem3260895 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) : t x.
Proof. exact (proj2 (@lem3260641 _85450 s t P x h1)). Qed.
Lemma lem3260896 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) : term108 _85450 t x.
Proof. exact (fun h0 : term88 _85450 t x => @lem3260895 _85450 s t P x h1). Qed.
Lemma lem3260898 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3260899 {_85450 : Type'} (t : _85450 -> Prop) (x : _85450) : (term108 _85450 t x) = (t x).
Proof. exact (@lem3260898 (t x)). Qed.
Lemma lem3260900 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) : t x.
Proof. exact (EQ_MP (@lem3260899 _85450 t x) (@lem3260896 _85450 s t P x h1)). Qed.
Lemma lem3260903 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3260905 {_85450 : Type'} (t : _85450 -> Prop) (x : _85450) : (term88 _85450 t x) = (term110 _85450 t x).
Proof. exact (@lem3260903 (t x)). Qed.
Lemma lem3260908 {_85450 : Type'} (t : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) : term110 _85450 t x.
Proof. exact (EQ_MP (@lem3260905 _85450 t x) (@lem3260809 _85450 t x h1)). Qed.
Lemma lem3260911 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (@lem3260908 _85450 t x h1 (@lem3260900 _85450 s t P x h2)). Qed.
Lemma lem3260912 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term103 _85450 s t P x) : term111.
Proof. exact (fun h0 : ~ False => @lem3260911 _85450 s t P x h1 h2). Qed.
Lemma lem3260914 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3260915 : term111 = False.
Proof. exact (@lem3260914 False). Qed.
Lemma lem3260916 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3260915) (@lem3260912 _85450 s t P x h1 h2)). Qed.
Lemma lem3260918 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) : P x.
Proof. exact (proj2 (@lem3260639 _85450 s t P x h1)). Qed.
Lemma lem3260919 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) : term108 _85450 P x.
Proof. exact (fun h0 : term88 _85450 P x => @lem3260918 _85450 s t P x h1). Qed.
Lemma lem3260921 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3260922 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) : (term108 _85450 P x) = (P x).
Proof. exact (@lem3260921 (P x)). Qed.
Lemma lem3260923 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) : P x.
Proof. exact (EQ_MP (@lem3260922 _85450 P x) (@lem3260919 _85450 s t P x h1)). Qed.
Lemma lem3260926 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3260928 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) : (term88 _85450 P x) = (term110 _85450 P x).
Proof. exact (@lem3260926 (P x)). Qed.
Lemma lem3260931 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) : term110 _85450 P x.
Proof. exact (EQ_MP (@lem3260928 _85450 P x) (@lem3260817 _85450 P x h1)). Qed.
Lemma lem3260934 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (@lem3260931 _85450 P x h1 (@lem3260923 _85450 s t P x h2)). Qed.
Lemma lem3260935 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : term111.
Proof. exact (fun h0 : ~ False => @lem3260934 _85450 s t P x h1 h2). Qed.
Lemma lem3260937 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3260938 : term111 = False.
Proof. exact (@lem3260937 False). Qed.
Lemma lem3260939 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3260938) (@lem3260935 _85450 s t P x h1 h2)). Qed.
Lemma lem3260941 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term100 _85450 s t P x) : s x.
Proof. exact (proj1 (@lem3260653 _85450 s t P x h1)). Qed.
Lemma lem3260942 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term100 _85450 s t P x) : term108 _85450 s x.
Proof. exact (fun h0 : term88 _85450 s x => @lem3260941 _85450 s t P x h1). Qed.
Lemma lem3260944 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3260945 {_85450 : Type'} (s : _85450 -> Prop) (x : _85450) : (term108 _85450 s x) = (s x).
Proof. exact (@lem3260944 (s x)). Qed.
Lemma lem3260946 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term100 _85450 s t P x) : s x.
Proof. exact (EQ_MP (@lem3260945 _85450 s x) (@lem3260942 _85450 s t P x h1)). Qed.
Lemma lem3260949 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3260951 {_85450 : Type'} (s : _85450 -> Prop) (x : _85450) : (term88 _85450 s x) = (term110 _85450 s x).
Proof. exact (@lem3260949 (s x)). Qed.
Lemma lem3260954 {_85450 : Type'} (s : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) : term110 _85450 s x.
Proof. exact (EQ_MP (@lem3260951 _85450 s x) (@lem3260827 _85450 s x h1)). Qed.
Lemma lem3260957 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term100 _85450 s t P x) : False.
Proof. exact (@lem3260954 _85450 s x h1 (@lem3260946 _85450 s t P x h2)). Qed.
Lemma lem3260958 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term100 _85450 s t P x) : term111.
Proof. exact (fun h0 : ~ False => @lem3260957 _85450 s t P x h1 h2). Qed.
Lemma lem3260960 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3260961 : term111 = False.
Proof. exact (@lem3260960 False). Qed.
Lemma lem3260962 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term100 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3260961) (@lem3260958 _85450 s t P x h1 h2)). Qed.
Lemma lem3260964 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term100 _85450 s t P x) : t x.
Proof. exact (proj1 (@lem3260652 _85450 s t P x h1)). Qed.
Lemma lem3260965 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term100 _85450 s t P x) : term108 _85450 t x.
Proof. exact (fun h0 : term88 _85450 t x => @lem3260964 _85450 s t P x h1). Qed.
Lemma lem3260967 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3260968 {_85450 : Type'} (t : _85450 -> Prop) (x : _85450) : (term108 _85450 t x) = (t x).
Proof. exact (@lem3260967 (t x)). Qed.
Lemma lem3260969 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term100 _85450 s t P x) : t x.
Proof. exact (EQ_MP (@lem3260968 _85450 t x) (@lem3260965 _85450 s t P x h1)). Qed.
Lemma lem3260972 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3260974 {_85450 : Type'} (t : _85450 -> Prop) (x : _85450) : (term88 _85450 t x) = (term110 _85450 t x).
Proof. exact (@lem3260972 (t x)). Qed.
Lemma lem3260977 {_85450 : Type'} (t : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) : term110 _85450 t x.
Proof. exact (EQ_MP (@lem3260974 _85450 t x) (@lem3260837 _85450 t x h1)). Qed.
Lemma lem3260980 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term100 _85450 s t P x) : False.
Proof. exact (@lem3260977 _85450 t x h1 (@lem3260969 _85450 s t P x h2)). Qed.
Lemma lem3260981 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term100 _85450 s t P x) : term111.
Proof. exact (fun h0 : ~ False => @lem3260980 _85450 s t P x h1 h2). Qed.
Lemma lem3260983 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3260984 : term111 = False.
Proof. exact (@lem3260983 False). Qed.
Lemma lem3260985 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term100 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3260984) (@lem3260981 _85450 s t P x h1 h2)). Qed.
Lemma lem3260987 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term100 _85450 s t P x) : P x.
Proof. exact (proj2 (@lem3260652 _85450 s t P x h1)). Qed.
Lemma lem3260988 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term100 _85450 s t P x) : term108 _85450 P x.
Proof. exact (fun h0 : term88 _85450 P x => @lem3260987 _85450 s t P x h1). Qed.
Lemma lem3260990 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3260991 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) : (term108 _85450 P x) = (P x).
Proof. exact (@lem3260990 (P x)). Qed.
Lemma lem3260992 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term100 _85450 s t P x) : P x.
Proof. exact (EQ_MP (@lem3260991 _85450 P x) (@lem3260988 _85450 s t P x h1)). Qed.
Lemma lem3260995 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3260997 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) : (term88 _85450 P x) = (term110 _85450 P x).
Proof. exact (@lem3260995 (P x)). Qed.
Lemma lem3261000 {_85450 : Type'} (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) : term110 _85450 P x.
Proof. exact (EQ_MP (@lem3260997 _85450 P x) (@lem3260847 _85450 P x h1)). Qed.
Lemma lem3261003 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term100 _85450 s t P x) : False.
Proof. exact (@lem3261000 _85450 P x h1 (@lem3260992 _85450 s t P x h2)). Qed.
Lemma lem3261004 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term100 _85450 s t P x) : term111.
Proof. exact (fun h0 : ~ False => @lem3261003 _85450 s t P x h1 h2). Qed.
Lemma lem3261006 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3261007 : term111 = False.
Proof. exact (@lem3261006 False). Qed.
Lemma lem3261008 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term100 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261007) (@lem3261004 _85450 s t P x h1 h2)). Qed.
Lemma lem3261009 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term100 _85450 s t P x) : (term88 _85450 P x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 P x => @lem3261008 _85450 s t P x h1 h2) (fun h3 : False => @lem3260847 _85450 P x h1)). Qed.
Lemma lem3261010 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term100 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261009 _85450 s t P x h1 h2) (@lem3260847 _85450 P x h1)). Qed.
Lemma lem3261011 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term100 _85450 s t P x) : (term88 _85450 t x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 t x => @lem3260985 _85450 s t P x h1 h2) (fun h3 : False => @lem3260837 _85450 t x h1)). Qed.
Lemma lem3261012 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term100 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261011 _85450 s t P x h1 h2) (@lem3260837 _85450 t x h1)). Qed.
Lemma lem3261013 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term100 _85450 s t P x) : (term88 _85450 s x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 s x => @lem3260962 _85450 s t P x h1 h2) (fun h3 : False => @lem3260827 _85450 s x h1)). Qed.
Lemma lem3261014 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term100 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261013 _85450 s t P x h1 h2) (@lem3260827 _85450 s x h1)). Qed.
Lemma lem3261015 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : (term88 _85450 P x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 P x => @lem3260939 _85450 s t P x h1 h2) (fun h3 : False => @lem3260817 _85450 P x h1)). Qed.
Lemma lem3261016 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261015 _85450 s t P x h1 h2) (@lem3260817 _85450 P x h1)). Qed.
Lemma lem3261017 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term103 _85450 s t P x) : (term88 _85450 t x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 t x => @lem3260916 _85450 s t P x h1 h2) (fun h3 : False => @lem3260809 _85450 t x h1)). Qed.
Lemma lem3261018 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261017 _85450 s t P x h1 h2) (@lem3260809 _85450 t x h1)). Qed.
Lemma lem3261019 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : (term88 _85450 P x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 P x => @lem3260893 _85450 s t P x h1 h2) (fun h3 : False => @lem3260801 _85450 P x h1)). Qed.
Lemma lem3261020 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261019 _85450 s t P x h1 h2) (@lem3260801 _85450 P x h1)). Qed.
Lemma lem3261021 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term103 _85450 s t P x) : (term88 _85450 s x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 s x => @lem3260870 _85450 s t P x h1 h2) (fun h3 : False => @lem3260793 _85450 s x h1)). Qed.
Lemma lem3261022 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261021 _85450 s t P x h1 h2) (@lem3260793 _85450 s x h1)). Qed.
Lemma lem3261023 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term100 _85450 s t P x) : (term88 _85450 P x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 P x => @lem3261010 _85450 s t P x h1 h2) (fun h3 : False => @lem3260785 _85450 P x h1)). Qed.
Lemma lem3261024 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term100 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261023 _85450 s t P x h1 h2) (@lem3260785 _85450 P x h1)). Qed.
Lemma lem3261025 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term100 _85450 s t P x) : (term88 _85450 t x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 t x => @lem3261012 _85450 s t P x h1 h2) (fun h3 : False => @lem3260765 _85450 t x h1)). Qed.
Lemma lem3261026 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term100 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261025 _85450 s t P x h1 h2) (@lem3260765 _85450 t x h1)). Qed.
Lemma lem3261027 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term100 _85450 s t P x) : (term88 _85450 s x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 s x => @lem3261014 _85450 s t P x h1 h2) (fun h3 : False => @lem3260745 _85450 s x h1)). Qed.
Lemma lem3261028 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term100 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261027 _85450 s t P x h1 h2) (@lem3260745 _85450 s x h1)). Qed.
Lemma lem3261029 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : (term88 _85450 P x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 P x => @lem3261016 _85450 s t P x h1 h2) (fun h3 : False => @lem3260725 _85450 P x h1)). Qed.
Lemma lem3261030 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261029 _85450 s t P x h1 h2) (@lem3260725 _85450 P x h1)). Qed.
Lemma lem3261031 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term103 _85450 s t P x) : (term88 _85450 t x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 t x => @lem3261018 _85450 s t P x h1 h2) (fun h3 : False => @lem3260709 _85450 t x h1)). Qed.
Lemma lem3261032 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261031 _85450 s t P x h1 h2) (@lem3260709 _85450 t x h1)). Qed.
Lemma lem3261033 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : (term88 _85450 P x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 P x => @lem3261020 _85450 s t P x h1 h2) (fun h3 : False => @lem3260693 _85450 P x h1)). Qed.
Lemma lem3261034 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261033 _85450 s t P x h1 h2) (@lem3260693 _85450 P x h1)). Qed.
Lemma lem3261035 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term103 _85450 s t P x) : (term88 _85450 s x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 s x => @lem3261022 _85450 s t P x h1 h2) (fun h3 : False => @lem3260677 _85450 s x h1)). Qed.
Lemma lem3261036 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261035 _85450 s t P x h1 h2) (@lem3260677 _85450 s x h1)). Qed.
Lemma lem3261037 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term100 _85450 s t P x) : (term88 _85450 P x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 P x => @lem3261024 _85450 s t P x h1 h2) (fun h3 : False => @lem3260785 _85450 P x h1)). Qed.
Lemma lem3261038 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term100 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261037 _85450 s t P x h1 h2) (@lem3260785 _85450 P x h1)). Qed.
Lemma lem3261039 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term100 _85450 s t P x) : (term88 _85450 t x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 t x => @lem3261026 _85450 s t P x h1 h2) (fun h3 : False => @lem3260765 _85450 t x h1)). Qed.
Lemma lem3261040 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term100 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261039 _85450 s t P x h1 h2) (@lem3260765 _85450 t x h1)). Qed.
Lemma lem3261041 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term100 _85450 s t P x) : (term88 _85450 s x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 s x => @lem3261028 _85450 s t P x h1 h2) (fun h3 : False => @lem3260745 _85450 s x h1)). Qed.
Lemma lem3261042 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term100 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261041 _85450 s t P x h1 h2) (@lem3260745 _85450 s x h1)). Qed.
Lemma lem3261043 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : (term88 _85450 P x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 P x => @lem3261030 _85450 s t P x h1 h2) (fun h3 : False => @lem3260725 _85450 P x h1)). Qed.
Lemma lem3261044 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261043 _85450 s t P x h1 h2) (@lem3260725 _85450 P x h1)). Qed.
Lemma lem3261045 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term103 _85450 s t P x) : (term88 _85450 t x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 t x => @lem3261032 _85450 s t P x h1 h2) (fun h3 : False => @lem3260709 _85450 t x h1)). Qed.
Lemma lem3261046 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 t x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261045 _85450 s t P x h1 h2) (@lem3260709 _85450 t x h1)). Qed.
Lemma lem3261047 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : (term88 _85450 P x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 P x => @lem3261034 _85450 s t P x h1 h2) (fun h3 : False => @lem3260693 _85450 P x h1)). Qed.
Lemma lem3261048 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 P x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261047 _85450 s t P x h1 h2) (@lem3260693 _85450 P x h1)). Qed.
Lemma lem3261049 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term103 _85450 s t P x) : (term88 _85450 s x) = False.
Proof. exact (prop_ext (fun h3 : term88 _85450 s x => @lem3261036 _85450 s t P x h1 h2) (fun h3 : False => @lem3260677 _85450 s x h1)). Qed.
Lemma lem3261050 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term88 _85450 s x) (h2 : term103 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261049 _85450 s t P x h1 h2) (@lem3260677 _85450 s x h1)). Qed.
Lemma lem3261051 {_85450 : Type'} (P : _85450 -> Prop) (s : _85450 -> Prop) (t : _85450 -> Prop) (x : _85450) (h1 : term100 _85450 s t P x) (h2 : term87 _85450 s t x) : False.
Proof. exact (or_elim (@lem3260658 _85450 s t x h2) (fun h0 : term88 _85450 s x => @lem3261042 _85450 s t P x h0 h1) (fun h0 : term88 _85450 t x => @lem3261040 _85450 s t P x h0 h1)). Qed.
Lemma lem3261052 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term100 _85450 s t P x) : False.
Proof. exact (or_elim (@lem3260651 _85450 s t P x h1) (fun h0 : term87 _85450 s t x => @lem3261051 _85450 P s t x h1 h0) (fun h0 : term88 _85450 P x => @lem3261038 _85450 s t P x h0 h1)). Qed.
Lemma lem3261053 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) (h2 : term87 _85450 t P x) : False.
Proof. exact (or_elim (@lem3260645 _85450 t P x h2) (fun h0 : term88 _85450 t x => @lem3261046 _85450 s t P x h0 h1) (fun h0 : term88 _85450 P x => @lem3261044 _85450 s t P x h0 h1)). Qed.
Lemma lem3261054 {_85450 : Type'} (t : _85450 -> Prop) (s : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) (h2 : term87 _85450 s P x) : False.
Proof. exact (or_elim (@lem3260644 _85450 s P x h2) (fun h0 : term88 _85450 s x => @lem3261050 _85450 s t P x h0 h1) (fun h0 : term88 _85450 P x => @lem3261048 _85450 s t P x h0 h1)). Qed.
Lemma lem3261055 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term103 _85450 s t P x) : False.
Proof. exact (or_elim (@lem3260638 _85450 s t P x h1) (fun h0 : term87 _85450 s P x => @lem3261054 _85450 t s P x h1 h0) (fun h0 : term87 _85450 t P x => @lem3261053 _85450 s t P x h1 h0)). Qed.
Lemma lem3261056 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term85 _85450 s t P x) : False.
Proof. exact (or_elim (@lem3260635 _85450 s t P x h1) (fun h0 : term103 _85450 s t P x => @lem3261055 _85450 s t P x h0) (fun h0 : term100 _85450 s t P x => @lem3261052 _85450 s t P x h0)). Qed.
Lemma lem3261057 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term85 _85450 s t P x) : (term85 _85450 s t P x) = False.
Proof. exact (prop_ext (fun h2 : term85 _85450 s t P x => @lem3261056 _85450 s t P x h1) (fun h2 : False => @lem3260469 _85450 s t P x h1)). Qed.
Lemma lem3261058 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) (h1 : term85 _85450 s t P x) : False.
Proof. exact (EQ_MP (@lem3261057 _85450 s t P x h1) (@lem3260469 _85450 s t P x h1)). Qed.
Lemma lem3261059 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : term84 _85450 s t P x.
Proof. exact (fun h0 : term85 _85450 s t P x => @lem3261058 _85450 s t P x h0). Qed.
Lemma lem3261060 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) (x : _85450) : (term42 _85450 s t P x) = (term66 _85450 s t P x).
Proof. exact (EQ_MP (@lem3260468 _85450 s t P x) (@lem3261059 _85450 s t P x)). Qed.
Lemma lem3261065 {_85450 : Type'} (s : _85450 -> Prop) (t : _85450 -> Prop) (P : _85450 -> Prop) : term69 _85450 s t P.
Proof. exact (fun x : _85450 => @lem3261060 _85450 s t P x). Qed.
Lemma lem3261070 {_85450 : Type'} (s : _85450 -> Prop) (P : _85450 -> Prop) : term71 _85450 s P.
Proof. exact (fun t : _85450 -> Prop => @lem3261065 _85450 s t P). Qed.
Lemma lem3261075 {_85450 : Type'} (P : _85450 -> Prop) : term73 _85450 P.
Proof. exact (fun s : _85450 -> Prop => @lem3261070 _85450 s P). Qed.
Lemma lem3261080 {_85450 : Type'} : term75 _85450.
Proof. exact (fun P : _85450 -> Prop => @lem3261075 _85450 P). Qed.
Lemma lem3261081 {_85450 : Type'} : term77 _85450.
Proof. exact (EQ_MP (@lem3260464 _85450) (@lem3261080 _85450)). Qed.
Lemma lem3261083 {_85450 : Type'} : term77 _85450.
Proof. exact (@lem3260352 _85450 (@lem3261081 _85450)). Qed.
Lemma lem3261084 {_85450 : Type'} (h1 : term78 _85450) : False.
Proof. exact (@lem3261083 _85450 (@lem3260336 _85450 h1)). Qed.
Lemma lem3261085 {_85450 : Type'} (h1 : term78 _85450) : (term78 _85450) = False.
Proof. exact (prop_ext (fun h2 : term78 _85450 => @lem3261084 _85450 h1) (fun h2 : False => @lem3260336 _85450 h1)). Qed.
Lemma lem3261086 {_85450 : Type'} (h1 : term78 _85450) : False.
Proof. exact (EQ_MP (@lem3261085 _85450 h1) (@lem3260336 _85450 h1)). Qed.
Lemma lem3261087 {_85450 : Type'} : term77 _85450.
Proof. exact (fun h0 : term78 _85450 => @lem3261086 _85450 h0). Qed.
Lemma lem3261088 {_85450 : Type'} : term75 _85450.
Proof. exact (EQ_MP (@lem3260335 _85450) (@lem3261087 _85450)). Qed.
Lemma lem3261089 {_85450 : Type'} : term15 _85450.
Proof. exact (EQ_MP (@lem3260331 _85450) (@lem3261088 _85450)). Qed.
Lemma lem3261090 {_85450 : Type'} : term14 _85450.
Proof. exact (EQ_MP (@lem3260147 _85450) (@lem3261089 _85450)). Qed.
