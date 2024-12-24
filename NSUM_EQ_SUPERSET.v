Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_EQ_SUPERSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import NSUM_EQ_spec.
Require Import NSUM_SUPERSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem6986990 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem6986991 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem6986992 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem6986991 t1) (@lem6986990 t1)). Qed.
Lemma lem6986993 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem6986992 t1 t2). Qed.
Lemma lem6986994 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem6986995 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem6986994 t1 t2) (@lem6986993 t1 t2)). Qed.
Lemma lem6986996 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem6986995 t1 t2 t3). Qed.
Lemma lem6986997 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem6986998 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem6986997 t1 t2 t3) (@lem6986996 t1 t2 t3)). Qed.
Lemma lem6986999 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem6986998 t1 t2 t3)). Qed.
Lemma lem6987001 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6987002 {A : Type'} (g : A -> nat) : (term8 A g) = (term9 A g).
Proof. exact (@lem6987001 (term8 A g)). Qed.
Lemma lem6987003 {A : Type'} (g : A -> nat) : (term9 A g) = (term8 A g).
Proof. exact (SYM (@lem6987002 A g)). Qed.
Lemma lem6987004 {A : Type'} (g : A -> nat) (h1 : term10 A g) : term10 A g.
Proof. exact (h1). Qed.
Lemma lem6987005 {A : Type'} : term11 A.
Proof. exact (@lem6962131 A). Qed.
Lemma lem6987008 {A : Type'} : term12 A.
Proof. exact (@lem6938831 A). Qed.
Lemma lem6987012 {_127166 A : Type'} (g : A -> nat) (h1 : term13 _127166 A g) : term13 _127166 A g.
Proof. exact (h1). Qed.
Lemma lem6987013 {_127166 A : Type'} (g : A -> nat) : term14 _127166 A g.
Proof. exact (fun h0 : term13 _127166 A g => @lem6987012 _127166 A g h0). Qed.
Lemma lem6987014 {_127166 A : Type'} (g : A -> nat) (h1 : term14 _127166 A g) : term14 _127166 A g.
Proof. exact (h1). Qed.
Lemma lem6987015 {_127166 A : Type'} (g : A -> nat) (h1 : term13 _127166 A g) : term13 _127166 A g.
Proof. exact (h1). Qed.
Lemma lem6987016 {_127166 A : Type'} (g : A -> nat) (h1 : term13 _127166 A g) (h2 : term14 _127166 A g) : term13 _127166 A g.
Proof. exact (@lem6987014 _127166 A g h2 (@lem6987015 _127166 A g h1)). Qed.
Lemma lem6987017 {_127166 A : Type'} (g : A -> nat) (h1 : term13 _127166 A g) : term15 _127166 A g.
Proof. exact (fun h0 : term14 _127166 A g => @lem6987016 _127166 A g h1 h0). Qed.
Lemma lem6987018 {_127166 A : Type'} (g : A -> nat) (h1 : term14 _127166 A g) : term14 _127166 A g.
Proof. exact (h1). Qed.
Lemma lem6987019 {_127166 A : Type'} (g : A -> nat) (h1 : term13 _127166 A g) (h2 : term14 _127166 A g) : term13 _127166 A g.
Proof. exact (@lem6987017 _127166 A g h1 (@lem6987018 _127166 A g h2)). Qed.
Lemma lem6987020 {_127166 A : Type'} (g : A -> nat) (h1 : term14 _127166 A g) : term14 _127166 A g.
Proof. exact (fun h0 : term13 _127166 A g => @lem6987019 _127166 A g h0 h1). Qed.
Lemma lem6987021 {_127166 A : Type'} (g : A -> nat) : term16 _127166 A g.
Proof. exact (fun h0 : term14 _127166 A g => @lem6987020 _127166 A g h0). Qed.
Lemma lem6987024 {_127166 A : Type'} (g : A -> nat) : term14 _127166 A g.
Proof. exact (@lem6987021 _127166 A g (@lem6987013 _127166 A g)). Qed.
Lemma lem6987025 {_127166 A : Type'} (g : A -> nat) : term14 _127166 A g.
Proof. exact (@lem6987024 _127166 A g). Qed.
Lemma lem6987111 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6987112 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem6987111 (term11 A)). Qed.
Lemma lem6987137 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem6987138 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem6987137 A) (@lem6987112 A)). Qed.
Lemma lem6987141 {_127166 : Type'} : (term19 _127166) = (term19 _127166).
Proof. exact (eq_refl (term19 _127166)). Qed.
Lemma lem6987142 {_127166 A : Type'} : (term22 _127166 A) = (term23 _127166 A).
Proof. exact (MK_COMB (@lem6987141 _127166) (@lem6987138 A)). Qed.
Lemma lem6987145 {A : Type'} (g : A -> nat) : (term24 A g) = (term24 A g).
Proof. exact (eq_refl (term24 A g)). Qed.
Lemma lem6987146 {_127166 A : Type'} (g : A -> nat) : (term13 _127166 A g) = (term25 _127166 A g).
Proof. exact (MK_COMB (@lem6987145 A g) (@lem6987142 _127166 A)). Qed.
Lemma lem6987149 {_127166 A : Type'} : (term26 _127166 A) = (term27 _127166 A).
Proof. exact (fun_ext (fun g : A -> nat => @lem6987146 _127166 A g)). Qed.
Lemma lem6987150 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6987159 {_127166 A : Type'} : (term28 _127166 A) = (term29 _127166 A).
Proof. exact (MK_COMB (@lem6987150 A) (@lem6987149 _127166 A)). Qed.
Lemma lem6987160 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((@nsum A v f) = (@nsum A u f)) = ((@nsum A v f) = (@nsum A u f)).
Proof. exact (eq_refl ((@nsum A v f) = (@nsum A u f))). Qed.
Lemma lem6987171 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term30 A v u f x) = (term30 A v u f x).
Proof. exact (eq_refl (term30 A v u f x)). Qed.
Lemma lem6987172 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term31 A v u f) = (term31 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6987171 A v u f x)). Qed.
Lemma lem6987173 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6987174 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term32 A v u f) = (term32 A v u f).
Proof. exact (MK_COMB (@lem6987173 A) (@lem6987172 A v u f)). Qed.
Lemma lem6987177 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term33 A u v) = (term33 A u v).
Proof. exact (eq_refl (term33 A u v)). Qed.
Lemma lem6987178 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term34 A v u f) = (term34 A v u f).
Proof. exact (MK_COMB (@lem6987177 A u v) (@lem6987174 A v u f)). Qed.
Lemma lem6987179 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6987180 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term35 A v u f) = (term35 A v u f).
Proof. exact (MK_COMB (@lem6987179) (@lem6987178 A v u f)). Qed.
Lemma lem6987181 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term36 A v u f) = (term36 A v u f).
Proof. exact (MK_COMB (@lem6987180 A v u f) (@lem6987160 A v u f)). Qed.
Lemma lem6987182 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term37 A u f) = (term37 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6987181 A v u f)). Qed.
Lemma lem6987183 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6987184 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term38 A u f) = (term38 A u f).
Proof. exact (MK_COMB (@lem6987183 A) (@lem6987182 A u f)). Qed.
Lemma lem6987185 {A : Type'} (f : A -> nat) : (term39 A f) = (term39 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6987184 A u f)). Qed.
Lemma lem6987186 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6987187 {A : Type'} (f : A -> nat) : (term40 A f) = (term40 A f).
Proof. exact (MK_COMB (@lem6987186 A) (@lem6987185 A f)). Qed.
Lemma lem6987188 {A : Type'} : (term41 A) = (term41 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6987187 A f)). Qed.
Lemma lem6987189 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6987190 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem6987189 A) (@lem6987188 A)). Qed.
Lemma lem6987191 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6987192 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem6987191) (@lem6987190 A)). Qed.
Lemma lem6987193 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : ((@nsum A s f) = (@nsum A s g)) = ((@nsum A s f) = (@nsum A s g)).
Proof. exact (eq_refl ((@nsum A s f) = (@nsum A s g))). Qed.
Lemma lem6987198 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term42 A s f g x) = (term42 A s f g x).
Proof. exact (eq_refl (term42 A s f g x)). Qed.
Lemma lem6987199 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term43 A s f g) = (term43 A s f g).
Proof. exact (fun_ext (fun x : A => @lem6987198 A s f g x)). Qed.
Lemma lem6987200 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6987201 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term44 A s f g) = (term44 A s f g).
Proof. exact (MK_COMB (@lem6987200 A) (@lem6987199 A s f g)). Qed.
Lemma lem6987202 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6987203 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term45 A s f g) = (term45 A s f g).
Proof. exact (MK_COMB (@lem6987202) (@lem6987201 A s f g)). Qed.
Lemma lem6987204 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term46 A f s g) = (term46 A f s g).
Proof. exact (MK_COMB (@lem6987203 A s f g) (@lem6987193 A f s g)). Qed.
Lemma lem6987205 {A : Type'} (f : A -> nat) (g : A -> nat) : (term47 A f g) = (term47 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6987204 A f s g)). Qed.
Lemma lem6987206 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6987207 {A : Type'} (f : A -> nat) (g : A -> nat) : (term48 A f g) = (term48 A f g).
Proof. exact (MK_COMB (@lem6987206 A) (@lem6987205 A f g)). Qed.
Lemma lem6987208 {A : Type'} (f : A -> nat) : (term49 A f) = (term49 A f).
Proof. exact (fun_ext (fun g : A -> nat => @lem6987207 A f g)). Qed.
Lemma lem6987209 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6987210 {A : Type'} (f : A -> nat) : (term50 A f) = (term50 A f).
Proof. exact (MK_COMB (@lem6987209 A) (@lem6987208 A f)). Qed.
Lemma lem6987211 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6987210 A f)). Qed.
Lemma lem6987212 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6987213 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem6987212 A) (@lem6987211 A)). Qed.
Lemma lem6987214 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6987215 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem6987214) (@lem6987213 A)). Qed.
Lemma lem6987216 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (MK_COMB (@lem6987215 A) (@lem6987192 A)). Qed.
Lemma lem6987217 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : ((@nsum _127166 s f) = (@nsum _127166 s g)) = ((@nsum _127166 s f) = (@nsum _127166 s g)).
Proof. exact (eq_refl ((@nsum _127166 s f) = (@nsum _127166 s g))). Qed.
Lemma lem6987222 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (x : _127166) : (term42 _127166 s f g x) = (term42 _127166 s f g x).
Proof. exact (eq_refl (term42 _127166 s f g x)). Qed.
Lemma lem6987223 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term43 _127166 s f g) = (term43 _127166 s f g).
Proof. exact (fun_ext (fun x : _127166 => @lem6987222 _127166 s f g x)). Qed.
Lemma lem6987224 {_127166 : Type'} : (@all _127166) = (@all _127166).
Proof. exact (eq_refl (@all _127166)). Qed.
Lemma lem6987225 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term44 _127166 s f g) = (term44 _127166 s f g).
Proof. exact (MK_COMB (@lem6987224 _127166) (@lem6987223 _127166 s f g)). Qed.
Lemma lem6987226 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6987227 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term45 _127166 s f g) = (term45 _127166 s f g).
Proof. exact (MK_COMB (@lem6987226) (@lem6987225 _127166 s f g)). Qed.
Lemma lem6987228 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term46 _127166 f s g) = (term46 _127166 f s g).
Proof. exact (MK_COMB (@lem6987227 _127166 s f g) (@lem6987217 _127166 f s g)). Qed.
Lemma lem6987229 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term47 _127166 f g) = (term47 _127166 f g).
Proof. exact (fun_ext (fun s : _127166 -> Prop => @lem6987228 _127166 f s g)). Qed.
Lemma lem6987230 {_127166 : Type'} : (@all (_127166 -> Prop)) = (@all (_127166 -> Prop)).
Proof. exact (eq_refl (@all (_127166 -> Prop))). Qed.
Lemma lem6987231 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term48 _127166 f g) = (term48 _127166 f g).
Proof. exact (MK_COMB (@lem6987230 _127166) (@lem6987229 _127166 f g)). Qed.
Lemma lem6987232 {_127166 : Type'} (f : _127166 -> nat) : (term49 _127166 f) = (term49 _127166 f).
Proof. exact (fun_ext (fun g : _127166 -> nat => @lem6987231 _127166 f g)). Qed.
Lemma lem6987233 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem6987234 {_127166 : Type'} (f : _127166 -> nat) : (term50 _127166 f) = (term50 _127166 f).
Proof. exact (MK_COMB (@lem6987233 _127166) (@lem6987232 _127166 f)). Qed.
Lemma lem6987235 {_127166 : Type'} : (term51 _127166) = (term51 _127166).
Proof. exact (fun_ext (fun f : _127166 -> nat => @lem6987234 _127166 f)). Qed.
Lemma lem6987236 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem6987237 {_127166 : Type'} : (term12 _127166) = (term12 _127166).
Proof. exact (MK_COMB (@lem6987236 _127166) (@lem6987235 _127166)). Qed.
Lemma lem6987238 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6987239 {_127166 : Type'} : (term19 _127166) = (term19 _127166).
Proof. exact (MK_COMB (@lem6987238) (@lem6987237 _127166)). Qed.
Lemma lem6987240 {_127166 A : Type'} : (term23 _127166 A) = (term23 _127166 A).
Proof. exact (MK_COMB (@lem6987239 _127166) (@lem6987216 A)). Qed.
Lemma lem6987241 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) : ((@nsum A s f) = (@nsum A t g)) = ((@nsum A s f) = (@nsum A t g)).
Proof. exact (eq_refl ((@nsum A s f) = (@nsum A t g))). Qed.
Lemma lem6987252 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) (x : A) : (term30 A s t f x) = (term30 A s t f x).
Proof. exact (eq_refl (term30 A s t f x)). Qed.
Lemma lem6987253 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term31 A s t f) = (term31 A s t f).
Proof. exact (fun_ext (fun x : A => @lem6987252 A s t f x)). Qed.
Lemma lem6987254 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6987255 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term32 A s t f) = (term32 A s t f).
Proof. exact (MK_COMB (@lem6987254 A) (@lem6987253 A s t f)). Qed.
Lemma lem6987260 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term42 A t f g x) = (term42 A t f g x).
Proof. exact (eq_refl (term42 A t f g x)). Qed.
Lemma lem6987261 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) : (term43 A t f g) = (term43 A t f g).
Proof. exact (fun_ext (fun x : A => @lem6987260 A t f g x)). Qed.
Lemma lem6987262 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6987263 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) : (term44 A t f g) = (term44 A t f g).
Proof. exact (MK_COMB (@lem6987262 A) (@lem6987261 A t f g)). Qed.
Lemma lem6987264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6987265 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) : (term52 A t f g) = (term52 A t f g).
Proof. exact (MK_COMB (@lem6987264) (@lem6987263 A t f g)). Qed.
Lemma lem6987266 {A : Type'} (g : A -> nat) (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term53 A g s t f) = (term53 A g s t f).
Proof. exact (MK_COMB (@lem6987265 A t f g) (@lem6987255 A s t f)). Qed.
Lemma lem6987269 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term33 A t s) = (term33 A t s).
Proof. exact (eq_refl (term33 A t s)). Qed.
Lemma lem6987270 {A : Type'} (g : A -> nat) (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term54 A g s t f) = (term54 A g s t f).
Proof. exact (MK_COMB (@lem6987269 A t s) (@lem6987266 A g s t f)). Qed.
Lemma lem6987273 {A : Type'} (t : A -> Prop) : (term55 A t) = (term55 A t).
Proof. exact (eq_refl (term55 A t)). Qed.
Lemma lem6987274 {A : Type'} (g : A -> nat) (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term56 A g s t f) = (term56 A g s t f).
Proof. exact (MK_COMB (@lem6987273 A t) (@lem6987270 A g s t f)). Qed.
Lemma lem6987275 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6987276 {A : Type'} (g : A -> nat) (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term57 A g s t f) = (term57 A g s t f).
Proof. exact (MK_COMB (@lem6987275) (@lem6987274 A g s t f)). Qed.
Lemma lem6987277 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) : (term58 A s f t g) = (term58 A s f t g).
Proof. exact (MK_COMB (@lem6987276 A g s t f) (@lem6987241 A s f t g)). Qed.
Lemma lem6987278 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term59 A s f g) = (term59 A s f g).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6987277 A s f t g)). Qed.
Lemma lem6987279 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6987280 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term60 A s f g) = (term60 A s f g).
Proof. exact (MK_COMB (@lem6987279 A) (@lem6987278 A s f g)). Qed.
Lemma lem6987281 {A : Type'} (f : A -> nat) (g : A -> nat) : (term61 A f g) = (term61 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6987280 A s f g)). Qed.
Lemma lem6987282 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6987283 {A : Type'} (f : A -> nat) (g : A -> nat) : (term62 A f g) = (term62 A f g).
Proof. exact (MK_COMB (@lem6987282 A) (@lem6987281 A f g)). Qed.
Lemma lem6987284 {A : Type'} (g : A -> nat) : (term63 A g) = (term63 A g).
Proof. exact (fun_ext (fun f : A -> nat => @lem6987283 A f g)). Qed.
Lemma lem6987285 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6987286 {A : Type'} (g : A -> nat) : (term8 A g) = (term8 A g).
Proof. exact (MK_COMB (@lem6987285 A) (@lem6987284 A g)). Qed.
Lemma lem6987287 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6987288 {A : Type'} (g : A -> nat) : (term10 A g) = (term10 A g).
Proof. exact (MK_COMB (@lem6987287) (@lem6987286 A g)). Qed.
Lemma lem6987289 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6987290 {A : Type'} (g : A -> nat) : (term24 A g) = (term24 A g).
Proof. exact (MK_COMB (@lem6987289) (@lem6987288 A g)). Qed.
Lemma lem6987291 {_127166 A : Type'} (g : A -> nat) : (term25 _127166 A g) = (term25 _127166 A g).
Proof. exact (MK_COMB (@lem6987290 A g) (@lem6987240 _127166 A)). Qed.
Lemma lem6987292 {_127166 A : Type'} : (term27 _127166 A) = (term27 _127166 A).
Proof. exact (fun_ext (fun g : A -> nat => @lem6987291 _127166 A g)). Qed.
Lemma lem6987293 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6987294 {_127166 A : Type'} : (term29 _127166 A) = (term29 _127166 A).
Proof. exact (MK_COMB (@lem6987293 A) (@lem6987292 _127166 A)). Qed.
Lemma lem6987441 {_127166 A : Type'} : (term28 _127166 A) = (term29 _127166 A).
Proof. exact (TRANS (@lem6987159 _127166 A) (@lem6987294 _127166 A)). Qed.
Lemma lem6987442 {_127166 A : Type'} : (term29 _127166 A) = (term28 _127166 A).
Proof. exact (SYM (@lem6987441 _127166 A)). Qed.
Lemma lem6987443 {A : Type'} (g : A -> nat) (h1 : term10 A g) : term10 A g.
Proof. exact (h1). Qed.
Lemma lem6987444 {_127166 : Type'} (h1 : term12 _127166) : term12 _127166.
Proof. exact (h1). Qed.
Lemma lem6987445 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem6987446 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem6987455 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term42 A t f g x) = (term64 A t f g x).
Proof. exact (@lem17265 (@IN A x t) ((f x) = (g x))). Qed.
Lemma lem6987456 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) : (term43 A t f g) = (term65 A t f g).
Proof. exact (fun_ext (fun x : A => @lem6987455 A t f g x)). Qed.
Lemma lem6987457 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6987458 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) : (term44 A t f g) = (term66 A t f g).
Proof. exact (MK_COMB (@lem6987457 A) (@lem6987456 A t f g)). Qed.
Lemma lem6987462 {A : Type'} (x : A) (t : A -> Prop) : (term67 A x t) = (@IN A x t).
Proof. exact (@lem16933 (@IN A x t)). Qed.
Lemma lem6987464 {A : Type'} (x : A) (s : A -> Prop) : (term68 A x s) = (term68 A x s).
Proof. exact (eq_refl (term68 A x s)). Qed.
Lemma lem6987465 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term69 A s x t) = (term70 A s x t).
Proof. exact (MK_COMB (@lem6987464 A x s) (@lem6987462 A x t)). Qed.
Lemma lem6987466 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term71 A s x t) = (term69 A s x t).
Proof. exact (@lem17045 (@IN A x s) (term72 A x t)). Qed.
Lemma lem6987467 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term71 A s x t) = (term70 A s x t).
Proof. exact (TRANS (@lem6987466 A s x t) (@lem6987465 A s x t)). Qed.
Lemma lem6987468 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((f x) = (NUMERAL 0)).
Proof. exact (eq_refl ((f x) = (NUMERAL 0))). Qed.
Lemma lem6987469 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6987470 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term73 A s x t) = (term74 A s x t).
Proof. exact (MK_COMB (@lem6987469) (@lem6987467 A s x t)). Qed.
Lemma lem6987471 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) (x : A) : (term75 A s t f x) = (term76 A s t f x).
Proof. exact (MK_COMB (@lem6987470 A s x t) (@lem6987468 A f x)). Qed.
Lemma lem6987472 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) (x : A) : (term30 A s t f x) = (term75 A s t f x).
Proof. exact (@lem17265 (term77 A s x t) ((f x) = (NUMERAL 0))). Qed.
Lemma lem6987473 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) (x : A) : (term30 A s t f x) = (term76 A s t f x).
Proof. exact (TRANS (@lem6987472 A s t f x) (@lem6987471 A s t f x)). Qed.
Lemma lem6987474 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term31 A s t f) = (term78 A s t f).
Proof. exact (fun_ext (fun x : A => @lem6987473 A s t f x)). Qed.
Lemma lem6987475 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6987476 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term32 A s t f) = (term79 A s t f).
Proof. exact (MK_COMB (@lem6987475 A) (@lem6987474 A s t f)). Qed.
Lemma lem6987477 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6987478 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) : (term52 A t f g) = (term80 A t f g).
Proof. exact (MK_COMB (@lem6987477) (@lem6987458 A t f g)). Qed.
Lemma lem6987479 {A : Type'} (g : A -> nat) (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term53 A g s t f) = (term81 A g s t f).
Proof. exact (MK_COMB (@lem6987478 A t f g) (@lem6987476 A s t f)). Qed.
Lemma lem6987481 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term33 A t s) = (term33 A t s).
Proof. exact (eq_refl (term33 A t s)). Qed.
Lemma lem6987482 {A : Type'} (g : A -> nat) (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term54 A g s t f) = (term82 A g s t f).
Proof. exact (MK_COMB (@lem6987481 A t s) (@lem6987479 A g s t f)). Qed.
Lemma lem6987484 {A : Type'} (t : A -> Prop) : (term55 A t) = (term55 A t).
Proof. exact (eq_refl (term55 A t)). Qed.
Lemma lem6987485 {A : Type'} (g : A -> nat) (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term56 A g s t f) = (term83 A g s t f).
Proof. exact (MK_COMB (@lem6987484 A t) (@lem6987482 A g s t f)). Qed.
Lemma lem6987486 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) : (term84 A s f t g) = (term84 A s f t g).
Proof. exact (eq_refl (term84 A s f t g)). Qed.
Lemma lem6987487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6987488 {A : Type'} (g : A -> nat) (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term85 A g s t f) = (term86 A g s t f).
Proof. exact (MK_COMB (@lem6987487) (@lem6987485 A g s t f)). Qed.
Lemma lem6987489 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) : (term87 A s f t g) = (term88 A s f t g).
Proof. exact (MK_COMB (@lem6987488 A g s t f) (@lem6987486 A s f t g)). Qed.
Lemma lem6987490 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) : (term89 A s f t g) = (term87 A s f t g).
Proof. exact (@lem17362 (term56 A g s t f) ((@nsum A s f) = (@nsum A t g))). Qed.
Lemma lem6987491 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) : (term89 A s f t g) = (term88 A s f t g).
Proof. exact (TRANS (@lem6987490 A s f t g) (@lem6987489 A s f t g)). Qed.
Lemma lem6987492 {A : Type'} (P : type686 A) : (term90 A P) = (term91 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem6987493 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term92 A s f g) = (term93 A s f g).
Proof. exact (@lem6987492 A (term59 A s f g)). Qed.
Lemma lem6987494 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) : (term94 A s f g t) = (term58 A s f t g).
Proof. exact (eq_refl (term94 A s f g t)). Qed.
Lemma lem6987495 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6987496 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) : (term95 A s f g t) = (term89 A s f t g).
Proof. exact (MK_COMB (@lem6987495) (@lem6987494 A s f t g)). Qed.
Lemma lem6987497 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) : (term95 A s f g t) = (term88 A s f t g).
Proof. exact (TRANS (@lem6987496 A s f t g) (@lem6987491 A s f t g)). Qed.
Lemma lem6987498 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term96 A s f g) = (term97 A s f g).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6987497 A s f t g)). Qed.
Lemma lem6987499 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem6987500 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term93 A s f g) = (term98 A s f g).
Proof. exact (MK_COMB (@lem6987499 A) (@lem6987498 A s f g)). Qed.
Lemma lem6987501 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term92 A s f g) = (term98 A s f g).
Proof. exact (TRANS (@lem6987493 A s f g) (@lem6987500 A s f g)). Qed.
Lemma lem6987502 {A : Type'} (P : type686 A) : (term90 A P) = (term91 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem6987503 {A : Type'} (f : A -> nat) (g : A -> nat) : (term99 A f g) = (term100 A f g).
Proof. exact (@lem6987502 A (term61 A f g)). Qed.
Lemma lem6987504 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term101 A f g s) = (term60 A s f g).
Proof. exact (eq_refl (term101 A f g s)). Qed.
Lemma lem6987505 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6987506 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term102 A f g s) = (term92 A s f g).
Proof. exact (MK_COMB (@lem6987505) (@lem6987504 A s f g)). Qed.
Lemma lem6987507 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term102 A f g s) = (term98 A s f g).
Proof. exact (TRANS (@lem6987506 A s f g) (@lem6987501 A s f g)). Qed.
Lemma lem6987508 {A : Type'} (f : A -> nat) (g : A -> nat) : (term103 A f g) = (term104 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6987507 A s f g)). Qed.
Lemma lem6987509 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem6987510 {A : Type'} (f : A -> nat) (g : A -> nat) : (term100 A f g) = (term105 A f g).
Proof. exact (MK_COMB (@lem6987509 A) (@lem6987508 A f g)). Qed.
Lemma lem6987511 {A : Type'} (f : A -> nat) (g : A -> nat) : (term99 A f g) = (term105 A f g).
Proof. exact (TRANS (@lem6987503 A f g) (@lem6987510 A f g)). Qed.
Lemma lem6987512 {A : Type'} (P : type704 A) : (term106 A P) = (term107 A P).
Proof. exact (@lem18392 (A -> nat) P). Qed.
Lemma lem6987513 {A : Type'} (g : A -> nat) : (term10 A g) = (term108 A g).
Proof. exact (@lem6987512 A (term63 A g)). Qed.
Lemma lem6987514 {A : Type'} (f : A -> nat) (g : A -> nat) : (term109 A g f) = (term62 A f g).
Proof. exact (eq_refl (term109 A g f)). Qed.
Lemma lem6987515 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6987516 {A : Type'} (f : A -> nat) (g : A -> nat) : (term110 A g f) = (term99 A f g).
Proof. exact (MK_COMB (@lem6987515) (@lem6987514 A f g)). Qed.
Lemma lem6987517 {A : Type'} (f : A -> nat) (g : A -> nat) : (term110 A g f) = (term105 A f g).
Proof. exact (TRANS (@lem6987516 A f g) (@lem6987511 A f g)). Qed.
Lemma lem6987518 {A : Type'} (g : A -> nat) : (term111 A g) = (term112 A g).
Proof. exact (fun_ext (fun f : A -> nat => @lem6987517 A f g)). Qed.
Lemma lem6987519 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem6987520 {A : Type'} (g : A -> nat) : (term108 A g) = (term113 A g).
Proof. exact (MK_COMB (@lem6987519 A) (@lem6987518 A g)). Qed.
Lemma lem6987677 {A : Type'} (g : A -> nat) : (term10 A g) = (term113 A g).
Proof. exact (TRANS (@lem6987513 A g) (@lem6987520 A g)). Qed.
Lemma lem6987678 {A : Type'} (g : A -> nat) (h1 : term10 A g) : term113 A g.
Proof. exact (EQ_MP (@lem6987677 A g) (@lem6987443 A g h1)). Qed.
Lemma lem6987685 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (x : _127166) : (term114 _127166 s f g x) = (term115 _127166 s f g x).
Proof. exact (@lem17362 (@IN _127166 x s) ((f x) = (g x))). Qed.
Lemma lem6987686 {_127166 : Type'} (P : _127166 -> Prop) : (term116 _127166 P) = (term117 _127166 P).
Proof. exact (@lem18392 _127166 P). Qed.
Lemma lem6987687 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term118 _127166 s f g) = (term119 _127166 s f g).
Proof. exact (@lem6987686 _127166 (term43 _127166 s f g)). Qed.
Lemma lem6987688 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (x : _127166) : (term120 _127166 s f g x) = (term42 _127166 s f g x).
Proof. exact (eq_refl (term120 _127166 s f g x)). Qed.
Lemma lem6987689 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6987690 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (x : _127166) : (term121 _127166 s f g x) = (term114 _127166 s f g x).
Proof. exact (MK_COMB (@lem6987689) (@lem6987688 _127166 s f g x)). Qed.
Lemma lem6987691 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (x : _127166) : (term121 _127166 s f g x) = (term115 _127166 s f g x).
Proof. exact (TRANS (@lem6987690 _127166 s f g x) (@lem6987685 _127166 s f g x)). Qed.
Lemma lem6987692 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term122 _127166 s f g) = (term123 _127166 s f g).
Proof. exact (fun_ext (fun x : _127166 => @lem6987691 _127166 s f g x)). Qed.
Lemma lem6987693 {_127166 : Type'} : (@ex _127166) = (@ex _127166).
Proof. exact (eq_refl (@ex _127166)). Qed.
Lemma lem6987694 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term119 _127166 s f g) = (term124 _127166 s f g).
Proof. exact (MK_COMB (@lem6987693 _127166) (@lem6987692 _127166 s f g)). Qed.
Lemma lem6987695 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term118 _127166 s f g) = (term124 _127166 s f g).
Proof. exact (TRANS (@lem6987687 _127166 s f g) (@lem6987694 _127166 s f g)). Qed.
Lemma lem6987696 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : ((@nsum _127166 s f) = (@nsum _127166 s g)) = ((@nsum _127166 s f) = (@nsum _127166 s g)).
Proof. exact (eq_refl ((@nsum _127166 s f) = (@nsum _127166 s g))). Qed.
Lemma lem6987697 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6987698 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term125 _127166 s f g) = (term126 _127166 s f g).
Proof. exact (MK_COMB (@lem6987697) (@lem6987695 _127166 s f g)). Qed.
Lemma lem6987699 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term127 _127166 f s g) = (term128 _127166 f s g).
Proof. exact (MK_COMB (@lem6987698 _127166 s f g) (@lem6987696 _127166 f s g)). Qed.
Lemma lem6987700 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term46 _127166 f s g) = (term127 _127166 f s g).
Proof. exact (@lem17265 (term44 _127166 s f g) ((@nsum _127166 s f) = (@nsum _127166 s g))). Qed.
Lemma lem6987701 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term46 _127166 f s g) = (term128 _127166 f s g).
Proof. exact (TRANS (@lem6987700 _127166 f s g) (@lem6987699 _127166 f s g)). Qed.
Lemma lem6987702 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term47 _127166 f g) = (term129 _127166 f g).
Proof. exact (fun_ext (fun s : _127166 -> Prop => @lem6987701 _127166 f s g)). Qed.
Lemma lem6987703 {_127166 : Type'} : (@all (_127166 -> Prop)) = (@all (_127166 -> Prop)).
Proof. exact (eq_refl (@all (_127166 -> Prop))). Qed.
Lemma lem6987704 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term48 _127166 f g) = (term130 _127166 f g).
Proof. exact (MK_COMB (@lem6987703 _127166) (@lem6987702 _127166 f g)). Qed.
Lemma lem6987705 {_127166 : Type'} (f : _127166 -> nat) : (term49 _127166 f) = (term131 _127166 f).
Proof. exact (fun_ext (fun g : _127166 -> nat => @lem6987704 _127166 f g)). Qed.
Lemma lem6987706 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem6987707 {_127166 : Type'} (f : _127166 -> nat) : (term50 _127166 f) = (term132 _127166 f).
Proof. exact (MK_COMB (@lem6987706 _127166) (@lem6987705 _127166 f)). Qed.
Lemma lem6987708 {_127166 : Type'} : (term51 _127166) = (term133 _127166).
Proof. exact (fun_ext (fun f : _127166 -> nat => @lem6987707 _127166 f)). Qed.
Lemma lem6987709 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem6987710 {_127166 : Type'} : (term12 _127166) = (term134 _127166).
Proof. exact (MK_COMB (@lem6987709 _127166) (@lem6987708 _127166)). Qed.
Lemma lem6987817 {A : Type'} (P : A -> Prop) (Q : Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6987818 {_127166 : Type'} (P : _127166 -> Prop) (Q : Prop) : (term135 _127166 P Q) = (term136 _127166 P Q).
Proof. exact (@lem6987817 _127166 P Q). Qed.
Lemma lem6987819 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term137 _127166 f s g) = (term138 _127166 f s g).
Proof. exact (@lem6987818 _127166 (term123 _127166 s f g) ((@nsum _127166 s f) = (@nsum _127166 s g))). Qed.
Lemma lem6987820 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (x : _127166) : (term139 _127166 s f g x) = (term115 _127166 s f g x).
Proof. exact (eq_refl (term139 _127166 s f g x)). Qed.
Lemma lem6987821 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term140 _127166 s f g) = (term123 _127166 s f g).
Proof. exact (fun_ext (fun x : _127166 => @lem6987820 _127166 s f g x)). Qed.
Lemma lem6987822 {_127166 : Type'} : (@ex _127166) = (@ex _127166).
Proof. exact (eq_refl (@ex _127166)). Qed.
Lemma lem6987823 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term141 _127166 s f g) = (term124 _127166 s f g).
Proof. exact (MK_COMB (@lem6987822 _127166) (@lem6987821 _127166 s f g)). Qed.
Lemma lem6987824 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6987825 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term142 _127166 s f g) = (term126 _127166 s f g).
Proof. exact (MK_COMB (@lem6987824) (@lem6987823 _127166 s f g)). Qed.
Lemma lem6987826 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : ((@nsum _127166 s f) = (@nsum _127166 s g)) = ((@nsum _127166 s f) = (@nsum _127166 s g)).
Proof. exact (eq_refl ((@nsum _127166 s f) = (@nsum _127166 s g))). Qed.
Lemma lem6987827 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term137 _127166 f s g) = (term128 _127166 f s g).
Proof. exact (MK_COMB (@lem6987825 _127166 s f g) (@lem6987826 _127166 f s g)). Qed.
Lemma lem6987828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6987829 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term143 _127166 f s g) = (term144 _127166 f s g).
Proof. exact (MK_COMB (@lem6987828) (@lem6987827 _127166 f s g)). Qed.
Lemma lem6987830 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (x : _127166) : (term139 _127166 s f g x) = (term115 _127166 s f g x).
Proof. exact (eq_refl (term139 _127166 s f g x)). Qed.
Lemma lem6987831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6987832 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (x : _127166) : (term145 _127166 s f g x) = (term146 _127166 s f g x).
Proof. exact (MK_COMB (@lem6987831) (@lem6987830 _127166 s f g x)). Qed.
Lemma lem6987833 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : ((@nsum _127166 s f) = (@nsum _127166 s g)) = ((@nsum _127166 s f) = (@nsum _127166 s g)).
Proof. exact (eq_refl ((@nsum _127166 s f) = (@nsum _127166 s g))). Qed.
Lemma lem6987834 {_127166 : Type'} (x : _127166) (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term147 _127166 x f s g) = (term148 _127166 x f s g).
Proof. exact (MK_COMB (@lem6987832 _127166 s f g x) (@lem6987833 _127166 f s g)). Qed.
Lemma lem6987835 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term149 _127166 f s g) = (term150 _127166 f s g).
Proof. exact (fun_ext (fun x : _127166 => @lem6987834 _127166 x f s g)). Qed.
Lemma lem6987836 {_127166 : Type'} : (@ex _127166) = (@ex _127166).
Proof. exact (eq_refl (@ex _127166)). Qed.
Lemma lem6987837 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term138 _127166 f s g) = (term151 _127166 f s g).
Proof. exact (MK_COMB (@lem6987836 _127166) (@lem6987835 _127166 f s g)). Qed.
Lemma lem6987838 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : ((term137 _127166 f s g) = (term138 _127166 f s g)) = ((term128 _127166 f s g) = (term151 _127166 f s g)).
Proof. exact (MK_COMB (@lem6987829 _127166 f s g) (@lem6987837 _127166 f s g)). Qed.
Lemma lem6987839 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term128 _127166 f s g) = (term151 _127166 f s g).
Proof. exact (EQ_MP (@lem6987838 _127166 f s g) (@lem6987819 _127166 f s g)). Qed.
Lemma lem6987840 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term129 _127166 f g) = (term152 _127166 f g).
Proof. exact (fun_ext (fun s : _127166 -> Prop => @lem6987839 _127166 f s g)). Qed.
Lemma lem6987841 {_127166 : Type'} : (@all (_127166 -> Prop)) = (@all (_127166 -> Prop)).
Proof. exact (eq_refl (@all (_127166 -> Prop))). Qed.
Lemma lem6987842 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term130 _127166 f g) = (term153 _127166 f g).
Proof. exact (MK_COMB (@lem6987841 _127166) (@lem6987840 _127166 f g)). Qed.
Lemma lem6987844 {A B : Type'} (P : type1413 A B) : (term154 A B P) = (term155 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6987845 {_127166 : Type'} (P : type672 _127166) : (term156 _127166 P) = (term157 _127166 P).
Proof. exact (@lem6987844 (_127166 -> Prop) _127166 P). Qed.
Lemma lem6987846 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term158 _127166 f g) = (term159 _127166 f g).
Proof. exact (@lem6987845 _127166 (term160 _127166 f g)). Qed.
Lemma lem6987847 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term161 _127166 f g s) = (term150 _127166 f s g).
Proof. exact (eq_refl (term161 _127166 f g s)). Qed.
Lemma lem6987848 {_127166 : Type'} (x : _127166) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6987849 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) (x : _127166) : (term162 _127166 f g s x) = (term163 _127166 f s g x).
Proof. exact (MK_COMB (@lem6987847 _127166 f s g) (@lem6987848 _127166 x)). Qed.
Lemma lem6987850 {_127166 : Type'} (x : _127166) (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term163 _127166 f s g x) = (term148 _127166 x f s g).
Proof. exact (eq_refl (term163 _127166 f s g x)). Qed.
Lemma lem6987851 {_127166 : Type'} (x : _127166) (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term162 _127166 f g s x) = (term148 _127166 x f s g).
Proof. exact (TRANS (@lem6987849 _127166 f s g x) (@lem6987850 _127166 x f s g)). Qed.
Lemma lem6987852 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term164 _127166 f g s) = (term150 _127166 f s g).
Proof. exact (fun_ext (fun x : _127166 => @lem6987851 _127166 x f s g)). Qed.
Lemma lem6987853 {_127166 : Type'} : (@ex _127166) = (@ex _127166).
Proof. exact (eq_refl (@ex _127166)). Qed.
Lemma lem6987854 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term165 _127166 f g s) = (term151 _127166 f s g).
Proof. exact (MK_COMB (@lem6987853 _127166) (@lem6987852 _127166 f s g)). Qed.
Lemma lem6987855 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term166 _127166 f g) = (term152 _127166 f g).
Proof. exact (fun_ext (fun s : _127166 -> Prop => @lem6987854 _127166 f s g)). Qed.
Lemma lem6987856 {_127166 : Type'} : (@all (_127166 -> Prop)) = (@all (_127166 -> Prop)).
Proof. exact (eq_refl (@all (_127166 -> Prop))). Qed.
Lemma lem6987857 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term158 _127166 f g) = (term153 _127166 f g).
Proof. exact (MK_COMB (@lem6987856 _127166) (@lem6987855 _127166 f g)). Qed.
Lemma lem6987858 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6987859 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term167 _127166 f g) = (term168 _127166 f g).
Proof. exact (MK_COMB (@lem6987858) (@lem6987857 _127166 f g)). Qed.
Lemma lem6987860 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term161 _127166 f g s) = (term150 _127166 f s g).
Proof. exact (eq_refl (term161 _127166 f g s)). Qed.
Lemma lem6987861 {_127166 : Type'} (x : type684 _127166) (s : _127166 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem6987862 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) (x : type684 _127166) (s : _127166 -> Prop) : (term169 _127166 f g x s) = (term170 _127166 f g x s).
Proof. exact (MK_COMB (@lem6987860 _127166 f s g) (@lem6987861 _127166 x s)). Qed.
Lemma lem6987863 {_127166 : Type'} (x : type684 _127166) (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term170 _127166 f g x s) = (term171 _127166 x f s g).
Proof. exact (eq_refl (term170 _127166 f g x s)). Qed.
Lemma lem6987864 {_127166 : Type'} (x : type684 _127166) (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term169 _127166 f g x s) = (term171 _127166 x f s g).
Proof. exact (TRANS (@lem6987862 _127166 f g x s) (@lem6987863 _127166 x f s g)). Qed.
Lemma lem6987865 {_127166 : Type'} (x : type684 _127166) (f : _127166 -> nat) (g : _127166 -> nat) : (term172 _127166 f g x) = (term173 _127166 x f g).
Proof. exact (fun_ext (fun s : _127166 -> Prop => @lem6987864 _127166 x f s g)). Qed.
Lemma lem6987866 {_127166 : Type'} : (@all (_127166 -> Prop)) = (@all (_127166 -> Prop)).
Proof. exact (eq_refl (@all (_127166 -> Prop))). Qed.
Lemma lem6987867 {_127166 : Type'} (x : type684 _127166) (f : _127166 -> nat) (g : _127166 -> nat) : (term174 _127166 f g x) = (term175 _127166 x f g).
Proof. exact (MK_COMB (@lem6987866 _127166) (@lem6987865 _127166 x f g)). Qed.
Lemma lem6987868 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term176 _127166 f g) = (term177 _127166 f g).
Proof. exact (fun_ext (fun x : type684 _127166 => @lem6987867 _127166 x f g)). Qed.
Lemma lem6987869 {_127166 : Type'} : (@ex ((_127166 -> Prop) -> _127166)) = (@ex ((_127166 -> Prop) -> _127166)).
Proof. exact (eq_refl (@ex ((_127166 -> Prop) -> _127166))). Qed.
Lemma lem6987870 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term159 _127166 f g) = (term178 _127166 f g).
Proof. exact (MK_COMB (@lem6987869 _127166) (@lem6987868 _127166 f g)). Qed.
Lemma lem6987871 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : ((term158 _127166 f g) = (term159 _127166 f g)) = ((term153 _127166 f g) = (term178 _127166 f g)).
Proof. exact (MK_COMB (@lem6987859 _127166 f g) (@lem6987870 _127166 f g)). Qed.
Lemma lem6987872 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term153 _127166 f g) = (term178 _127166 f g).
Proof. exact (EQ_MP (@lem6987871 _127166 f g) (@lem6987846 _127166 f g)). Qed.
Lemma lem6987873 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term130 _127166 f g) = (term178 _127166 f g).
Proof. exact (TRANS (@lem6987842 _127166 f g) (@lem6987872 _127166 f g)). Qed.
Lemma lem6987874 {_127166 : Type'} (f : _127166 -> nat) : (term131 _127166 f) = (term179 _127166 f).
Proof. exact (fun_ext (fun g : _127166 -> nat => @lem6987873 _127166 f g)). Qed.
Lemma lem6987875 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem6987876 {_127166 : Type'} (f : _127166 -> nat) : (term132 _127166 f) = (term180 _127166 f).
Proof. exact (MK_COMB (@lem6987875 _127166) (@lem6987874 _127166 f)). Qed.
Lemma lem6987878 {A B : Type'} (P : type1413 A B) : (term154 A B P) = (term155 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6987879 {_127166 : Type'} (P : type690 _127166) : (term181 _127166 P) = (term182 _127166 P).
Proof. exact (@lem6987878 (_127166 -> nat) (type684 _127166) P). Qed.
Lemma lem6987880 {_127166 : Type'} (f : _127166 -> nat) : (term183 _127166 f) = (term184 _127166 f).
Proof. exact (@lem6987879 _127166 (term185 _127166 f)). Qed.
Lemma lem6987881 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term186 _127166 f g) = (term177 _127166 f g).
Proof. exact (eq_refl (term186 _127166 f g)). Qed.
Lemma lem6987882 {_127166 : Type'} (x : type684 _127166) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6987883 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) (x : type684 _127166) : (term187 _127166 f g x) = (term188 _127166 f g x).
Proof. exact (MK_COMB (@lem6987881 _127166 f g) (@lem6987882 _127166 x)). Qed.
Lemma lem6987884 {_127166 : Type'} (x : type684 _127166) (f : _127166 -> nat) (g : _127166 -> nat) : (term188 _127166 f g x) = (term175 _127166 x f g).
Proof. exact (eq_refl (term188 _127166 f g x)). Qed.
Lemma lem6987885 {_127166 : Type'} (x : type684 _127166) (f : _127166 -> nat) (g : _127166 -> nat) : (term187 _127166 f g x) = (term175 _127166 x f g).
Proof. exact (TRANS (@lem6987883 _127166 f g x) (@lem6987884 _127166 x f g)). Qed.
Lemma lem6987886 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term189 _127166 f g) = (term177 _127166 f g).
Proof. exact (fun_ext (fun x : type684 _127166 => @lem6987885 _127166 x f g)). Qed.
Lemma lem6987887 {_127166 : Type'} : (@ex ((_127166 -> Prop) -> _127166)) = (@ex ((_127166 -> Prop) -> _127166)).
Proof. exact (eq_refl (@ex ((_127166 -> Prop) -> _127166))). Qed.
Lemma lem6987888 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term190 _127166 f g) = (term178 _127166 f g).
Proof. exact (MK_COMB (@lem6987887 _127166) (@lem6987886 _127166 f g)). Qed.
Lemma lem6987889 {_127166 : Type'} (f : _127166 -> nat) : (term191 _127166 f) = (term179 _127166 f).
Proof. exact (fun_ext (fun g : _127166 -> nat => @lem6987888 _127166 f g)). Qed.
Lemma lem6987890 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem6987891 {_127166 : Type'} (f : _127166 -> nat) : (term183 _127166 f) = (term180 _127166 f).
Proof. exact (MK_COMB (@lem6987890 _127166) (@lem6987889 _127166 f)). Qed.
Lemma lem6987892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6987893 {_127166 : Type'} (f : _127166 -> nat) : (term192 _127166 f) = (term193 _127166 f).
Proof. exact (MK_COMB (@lem6987892) (@lem6987891 _127166 f)). Qed.
Lemma lem6987894 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term186 _127166 f g) = (term177 _127166 f g).
Proof. exact (eq_refl (term186 _127166 f g)). Qed.
Lemma lem6987895 {_127166 : Type'} (x : type694 _127166) (g : _127166 -> nat) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem6987896 {_127166 : Type'} (f : _127166 -> nat) (x : type694 _127166) (g : _127166 -> nat) : (term194 _127166 f x g) = (term195 _127166 f x g).
Proof. exact (MK_COMB (@lem6987894 _127166 f g) (@lem6987895 _127166 x g)). Qed.
Lemma lem6987897 {_127166 : Type'} (x : type694 _127166) (f : _127166 -> nat) (g : _127166 -> nat) : (term195 _127166 f x g) = (term196 _127166 x f g).
Proof. exact (eq_refl (term195 _127166 f x g)). Qed.
Lemma lem6987898 {_127166 : Type'} (x : type694 _127166) (f : _127166 -> nat) (g : _127166 -> nat) : (term194 _127166 f x g) = (term196 _127166 x f g).
Proof. exact (TRANS (@lem6987896 _127166 f x g) (@lem6987897 _127166 x f g)). Qed.
Lemma lem6987899 {_127166 : Type'} (x : type694 _127166) (f : _127166 -> nat) : (term197 _127166 f x) = (term198 _127166 x f).
Proof. exact (fun_ext (fun g : _127166 -> nat => @lem6987898 _127166 x f g)). Qed.
Lemma lem6987900 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem6987901 {_127166 : Type'} (x : type694 _127166) (f : _127166 -> nat) : (term199 _127166 f x) = (term200 _127166 x f).
Proof. exact (MK_COMB (@lem6987900 _127166) (@lem6987899 _127166 x f)). Qed.
Lemma lem6987902 {_127166 : Type'} (f : _127166 -> nat) : (term201 _127166 f) = (term202 _127166 f).
Proof. exact (fun_ext (fun x : type694 _127166 => @lem6987901 _127166 x f)). Qed.
Lemma lem6987903 {_127166 : Type'} : (@ex ((_127166 -> nat) -> (_127166 -> Prop) -> _127166)) = (@ex ((_127166 -> nat) -> (_127166 -> Prop) -> _127166)).
Proof. exact (eq_refl (@ex ((_127166 -> nat) -> (_127166 -> Prop) -> _127166))). Qed.
Lemma lem6987904 {_127166 : Type'} (f : _127166 -> nat) : (term184 _127166 f) = (term203 _127166 f).
Proof. exact (MK_COMB (@lem6987903 _127166) (@lem6987902 _127166 f)). Qed.
Lemma lem6987905 {_127166 : Type'} (f : _127166 -> nat) : ((term183 _127166 f) = (term184 _127166 f)) = ((term180 _127166 f) = (term203 _127166 f)).
Proof. exact (MK_COMB (@lem6987893 _127166 f) (@lem6987904 _127166 f)). Qed.
Lemma lem6987906 {_127166 : Type'} (f : _127166 -> nat) : (term180 _127166 f) = (term203 _127166 f).
Proof. exact (EQ_MP (@lem6987905 _127166 f) (@lem6987880 _127166 f)). Qed.
Lemma lem6987907 {_127166 : Type'} (f : _127166 -> nat) : (term132 _127166 f) = (term203 _127166 f).
Proof. exact (TRANS (@lem6987876 _127166 f) (@lem6987906 _127166 f)). Qed.
Lemma lem6987908 {_127166 : Type'} : (term133 _127166) = (term204 _127166).
Proof. exact (fun_ext (fun f : _127166 -> nat => @lem6987907 _127166 f)). Qed.
Lemma lem6987909 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem6987910 {_127166 : Type'} : (term134 _127166) = (term205 _127166).
Proof. exact (MK_COMB (@lem6987909 _127166) (@lem6987908 _127166)). Qed.
Lemma lem6987912 {A B : Type'} (P : type1413 A B) : (term154 A B P) = (term155 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6987913 {_127166 : Type'} (P : type691 _127166) : (term206 _127166 P) = (term207 _127166 P).
Proof. exact (@lem6987912 (_127166 -> nat) (type694 _127166) P). Qed.
Lemma lem6987914 {_127166 : Type'} : (term208 _127166) = (term209 _127166).
Proof. exact (@lem6987913 _127166 (term210 _127166)). Qed.
Lemma lem6987915 {_127166 : Type'} (f : _127166 -> nat) : (term211 _127166 f) = (term202 _127166 f).
Proof. exact (eq_refl (term211 _127166 f)). Qed.
Lemma lem6987916 {_127166 : Type'} (x : type694 _127166) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6987917 {_127166 : Type'} (f : _127166 -> nat) (x : type694 _127166) : (term212 _127166 f x) = (term213 _127166 f x).
Proof. exact (MK_COMB (@lem6987915 _127166 f) (@lem6987916 _127166 x)). Qed.
Lemma lem6987918 {_127166 : Type'} (x : type694 _127166) (f : _127166 -> nat) : (term213 _127166 f x) = (term200 _127166 x f).
Proof. exact (eq_refl (term213 _127166 f x)). Qed.
Lemma lem6987919 {_127166 : Type'} (x : type694 _127166) (f : _127166 -> nat) : (term212 _127166 f x) = (term200 _127166 x f).
Proof. exact (TRANS (@lem6987917 _127166 f x) (@lem6987918 _127166 x f)). Qed.
Lemma lem6987920 {_127166 : Type'} (f : _127166 -> nat) : (term214 _127166 f) = (term202 _127166 f).
Proof. exact (fun_ext (fun x : type694 _127166 => @lem6987919 _127166 x f)). Qed.
Lemma lem6987921 {_127166 : Type'} : (@ex ((_127166 -> nat) -> (_127166 -> Prop) -> _127166)) = (@ex ((_127166 -> nat) -> (_127166 -> Prop) -> _127166)).
Proof. exact (eq_refl (@ex ((_127166 -> nat) -> (_127166 -> Prop) -> _127166))). Qed.
Lemma lem6987922 {_127166 : Type'} (f : _127166 -> nat) : (term215 _127166 f) = (term203 _127166 f).
Proof. exact (MK_COMB (@lem6987921 _127166) (@lem6987920 _127166 f)). Qed.
Lemma lem6987923 {_127166 : Type'} : (term216 _127166) = (term204 _127166).
Proof. exact (fun_ext (fun f : _127166 -> nat => @lem6987922 _127166 f)). Qed.
Lemma lem6987924 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem6987925 {_127166 : Type'} : (term208 _127166) = (term205 _127166).
Proof. exact (MK_COMB (@lem6987924 _127166) (@lem6987923 _127166)). Qed.
Lemma lem6987926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6987927 {_127166 : Type'} : (term217 _127166) = (term218 _127166).
Proof. exact (MK_COMB (@lem6987926) (@lem6987925 _127166)). Qed.
Lemma lem6987928 {_127166 : Type'} (f : _127166 -> nat) : (term211 _127166 f) = (term202 _127166 f).
Proof. exact (eq_refl (term211 _127166 f)). Qed.
Lemma lem6987929 {_127166 : Type'} (x : type695 _127166) (f : _127166 -> nat) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem6987930 {_127166 : Type'} (x : type695 _127166) (f : _127166 -> nat) : (term219 _127166 x f) = (term220 _127166 x f).
Proof. exact (MK_COMB (@lem6987928 _127166 f) (@lem6987929 _127166 x f)). Qed.
Lemma lem6987931 {_127166 : Type'} (x : type695 _127166) (f : _127166 -> nat) : (term220 _127166 x f) = (term221 _127166 x f).
Proof. exact (eq_refl (term220 _127166 x f)). Qed.
Lemma lem6987932 {_127166 : Type'} (x : type695 _127166) (f : _127166 -> nat) : (term219 _127166 x f) = (term221 _127166 x f).
Proof. exact (TRANS (@lem6987930 _127166 x f) (@lem6987931 _127166 x f)). Qed.
Lemma lem6987933 {_127166 : Type'} (x : type695 _127166) : (term222 _127166 x) = (term223 _127166 x).
Proof. exact (fun_ext (fun f : _127166 -> nat => @lem6987932 _127166 x f)). Qed.
Lemma lem6987934 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem6987935 {_127166 : Type'} (x : type695 _127166) : (term224 _127166 x) = (term225 _127166 x).
Proof. exact (MK_COMB (@lem6987934 _127166) (@lem6987933 _127166 x)). Qed.
Lemma lem6987936 {_127166 : Type'} : (term226 _127166) = (term227 _127166).
Proof. exact (fun_ext (fun x : type695 _127166 => @lem6987935 _127166 x)). Qed.
Lemma lem6987937 {_127166 : Type'} : (@ex ((_127166 -> nat) -> (_127166 -> nat) -> (_127166 -> Prop) -> _127166)) = (@ex ((_127166 -> nat) -> (_127166 -> nat) -> (_127166 -> Prop) -> _127166)).
Proof. exact (eq_refl (@ex ((_127166 -> nat) -> (_127166 -> nat) -> (_127166 -> Prop) -> _127166))). Qed.
Lemma lem6987938 {_127166 : Type'} : (term209 _127166) = (term228 _127166).
Proof. exact (MK_COMB (@lem6987937 _127166) (@lem6987936 _127166)). Qed.
Lemma lem6987939 {_127166 : Type'} : ((term208 _127166) = (term209 _127166)) = ((term205 _127166) = (term228 _127166)).
Proof. exact (MK_COMB (@lem6987927 _127166) (@lem6987938 _127166)). Qed.
Lemma lem6987940 {_127166 : Type'} : (term205 _127166) = (term228 _127166).
Proof. exact (EQ_MP (@lem6987939 _127166) (@lem6987914 _127166)). Qed.
Lemma lem6987942 {_127166 : Type'} : (term134 _127166) = (term228 _127166).
Proof. exact (TRANS (@lem6987910 _127166) (@lem6987940 _127166)). Qed.
Lemma lem6987943 {_127166 : Type'} : (term12 _127166) = (term228 _127166).
Proof. exact (TRANS (@lem6987710 _127166) (@lem6987942 _127166)). Qed.
Lemma lem6987944 {_127166 : Type'} (h1 : term12 _127166) : term228 _127166.
Proof. exact (EQ_MP (@lem6987943 _127166) (@lem6987444 _127166 h1)). Qed.
Lemma lem6987951 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term114 A s f g x) = (term115 A s f g x).
Proof. exact (@lem17362 (@IN A x s) ((f x) = (g x))). Qed.
Lemma lem6987952 {A : Type'} (P : A -> Prop) : (term116 A P) = (term117 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6987953 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term118 A s f g) = (term119 A s f g).
Proof. exact (@lem6987952 A (term43 A s f g)). Qed.
Lemma lem6987954 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term120 A s f g x) = (term42 A s f g x).
Proof. exact (eq_refl (term120 A s f g x)). Qed.
Lemma lem6987955 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6987956 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term121 A s f g x) = (term114 A s f g x).
Proof. exact (MK_COMB (@lem6987955) (@lem6987954 A s f g x)). Qed.
Lemma lem6987957 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term121 A s f g x) = (term115 A s f g x).
Proof. exact (TRANS (@lem6987956 A s f g x) (@lem6987951 A s f g x)). Qed.
Lemma lem6987958 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term122 A s f g) = (term123 A s f g).
Proof. exact (fun_ext (fun x : A => @lem6987957 A s f g x)). Qed.
Lemma lem6987959 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6987960 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term119 A s f g) = (term124 A s f g).
Proof. exact (MK_COMB (@lem6987959 A) (@lem6987958 A s f g)). Qed.
Lemma lem6987961 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term118 A s f g) = (term124 A s f g).
Proof. exact (TRANS (@lem6987953 A s f g) (@lem6987960 A s f g)). Qed.
Lemma lem6987962 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : ((@nsum A s f) = (@nsum A s g)) = ((@nsum A s f) = (@nsum A s g)).
Proof. exact (eq_refl ((@nsum A s f) = (@nsum A s g))). Qed.
Lemma lem6987963 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6987964 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term125 A s f g) = (term126 A s f g).
Proof. exact (MK_COMB (@lem6987963) (@lem6987961 A s f g)). Qed.
Lemma lem6987965 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term127 A f s g) = (term128 A f s g).
Proof. exact (MK_COMB (@lem6987964 A s f g) (@lem6987962 A f s g)). Qed.
Lemma lem6987966 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term46 A f s g) = (term127 A f s g).
Proof. exact (@lem17265 (term44 A s f g) ((@nsum A s f) = (@nsum A s g))). Qed.
Lemma lem6987967 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term46 A f s g) = (term128 A f s g).
Proof. exact (TRANS (@lem6987966 A f s g) (@lem6987965 A f s g)). Qed.
Lemma lem6987968 {A : Type'} (f : A -> nat) (g : A -> nat) : (term47 A f g) = (term129 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6987967 A f s g)). Qed.
Lemma lem6987969 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6987970 {A : Type'} (f : A -> nat) (g : A -> nat) : (term48 A f g) = (term130 A f g).
Proof. exact (MK_COMB (@lem6987969 A) (@lem6987968 A f g)). Qed.
Lemma lem6987971 {A : Type'} (f : A -> nat) : (term49 A f) = (term131 A f).
Proof. exact (fun_ext (fun g : A -> nat => @lem6987970 A f g)). Qed.
Lemma lem6987972 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6987973 {A : Type'} (f : A -> nat) : (term50 A f) = (term132 A f).
Proof. exact (MK_COMB (@lem6987972 A) (@lem6987971 A f)). Qed.
Lemma lem6987974 {A : Type'} : (term51 A) = (term133 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6987973 A f)). Qed.
Lemma lem6987975 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6987976 {A : Type'} : (term12 A) = (term134 A).
Proof. exact (MK_COMB (@lem6987975 A) (@lem6987974 A)). Qed.
Lemma lem6988083 {A : Type'} (P : A -> Prop) (Q : Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6988084 {A : Type'} (P : A -> Prop) (Q : Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (@lem6988083 A P Q). Qed.
Lemma lem6988085 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term137 A f s g) = (term138 A f s g).
Proof. exact (@lem6988084 A (term123 A s f g) ((@nsum A s f) = (@nsum A s g))). Qed.
Lemma lem6988086 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term139 A s f g x) = (term115 A s f g x).
Proof. exact (eq_refl (term139 A s f g x)). Qed.
Lemma lem6988087 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term140 A s f g) = (term123 A s f g).
Proof. exact (fun_ext (fun x : A => @lem6988086 A s f g x)). Qed.
Lemma lem6988088 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6988089 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term141 A s f g) = (term124 A s f g).
Proof. exact (MK_COMB (@lem6988088 A) (@lem6988087 A s f g)). Qed.
Lemma lem6988090 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6988091 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term142 A s f g) = (term126 A s f g).
Proof. exact (MK_COMB (@lem6988090) (@lem6988089 A s f g)). Qed.
Lemma lem6988092 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : ((@nsum A s f) = (@nsum A s g)) = ((@nsum A s f) = (@nsum A s g)).
Proof. exact (eq_refl ((@nsum A s f) = (@nsum A s g))). Qed.
Lemma lem6988093 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term137 A f s g) = (term128 A f s g).
Proof. exact (MK_COMB (@lem6988091 A s f g) (@lem6988092 A f s g)). Qed.
Lemma lem6988094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6988095 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term143 A f s g) = (term144 A f s g).
Proof. exact (MK_COMB (@lem6988094) (@lem6988093 A f s g)). Qed.
Lemma lem6988096 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term139 A s f g x) = (term115 A s f g x).
Proof. exact (eq_refl (term139 A s f g x)). Qed.
Lemma lem6988097 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6988098 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term145 A s f g x) = (term146 A s f g x).
Proof. exact (MK_COMB (@lem6988097) (@lem6988096 A s f g x)). Qed.
Lemma lem6988099 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : ((@nsum A s f) = (@nsum A s g)) = ((@nsum A s f) = (@nsum A s g)).
Proof. exact (eq_refl ((@nsum A s f) = (@nsum A s g))). Qed.
Lemma lem6988100 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term147 A x f s g) = (term148 A x f s g).
Proof. exact (MK_COMB (@lem6988098 A s f g x) (@lem6988099 A f s g)). Qed.
Lemma lem6988101 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term149 A f s g) = (term150 A f s g).
Proof. exact (fun_ext (fun x : A => @lem6988100 A x f s g)). Qed.
Lemma lem6988102 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6988103 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term138 A f s g) = (term151 A f s g).
Proof. exact (MK_COMB (@lem6988102 A) (@lem6988101 A f s g)). Qed.
Lemma lem6988104 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : ((term137 A f s g) = (term138 A f s g)) = ((term128 A f s g) = (term151 A f s g)).
Proof. exact (MK_COMB (@lem6988095 A f s g) (@lem6988103 A f s g)). Qed.
Lemma lem6988105 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term128 A f s g) = (term151 A f s g).
Proof. exact (EQ_MP (@lem6988104 A f s g) (@lem6988085 A f s g)). Qed.
Lemma lem6988106 {A : Type'} (f : A -> nat) (g : A -> nat) : (term129 A f g) = (term152 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6988105 A f s g)). Qed.
Lemma lem6988107 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6988108 {A : Type'} (f : A -> nat) (g : A -> nat) : (term130 A f g) = (term153 A f g).
Proof. exact (MK_COMB (@lem6988107 A) (@lem6988106 A f g)). Qed.
Lemma lem6988110 {A B : Type'} (P : type1413 A B) : (term154 A B P) = (term155 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6988111 {A : Type'} (P : type672 A) : (term156 A P) = (term157 A P).
Proof. exact (@lem6988110 (A -> Prop) A P). Qed.
Lemma lem6988112 {A : Type'} (f : A -> nat) (g : A -> nat) : (term158 A f g) = (term159 A f g).
Proof. exact (@lem6988111 A (term160 A f g)). Qed.
Lemma lem6988113 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term161 A f g s) = (term150 A f s g).
Proof. exact (eq_refl (term161 A f g s)). Qed.
Lemma lem6988114 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6988115 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term162 A f g s x) = (term163 A f s g x).
Proof. exact (MK_COMB (@lem6988113 A f s g) (@lem6988114 A x)). Qed.
Lemma lem6988116 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term163 A f s g x) = (term148 A x f s g).
Proof. exact (eq_refl (term163 A f s g x)). Qed.
Lemma lem6988117 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term162 A f g s x) = (term148 A x f s g).
Proof. exact (TRANS (@lem6988115 A f s g x) (@lem6988116 A x f s g)). Qed.
Lemma lem6988118 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term164 A f g s) = (term150 A f s g).
Proof. exact (fun_ext (fun x : A => @lem6988117 A x f s g)). Qed.
Lemma lem6988119 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6988120 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term165 A f g s) = (term151 A f s g).
Proof. exact (MK_COMB (@lem6988119 A) (@lem6988118 A f s g)). Qed.
Lemma lem6988121 {A : Type'} (f : A -> nat) (g : A -> nat) : (term166 A f g) = (term152 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6988120 A f s g)). Qed.
Lemma lem6988122 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6988123 {A : Type'} (f : A -> nat) (g : A -> nat) : (term158 A f g) = (term153 A f g).
Proof. exact (MK_COMB (@lem6988122 A) (@lem6988121 A f g)). Qed.
Lemma lem6988124 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6988125 {A : Type'} (f : A -> nat) (g : A -> nat) : (term167 A f g) = (term168 A f g).
Proof. exact (MK_COMB (@lem6988124) (@lem6988123 A f g)). Qed.
Lemma lem6988126 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term161 A f g s) = (term150 A f s g).
Proof. exact (eq_refl (term161 A f g s)). Qed.
Lemma lem6988127 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem6988128 {A : Type'} (f : A -> nat) (g : A -> nat) (x : type684 A) (s : A -> Prop) : (term169 A f g x s) = (term170 A f g x s).
Proof. exact (MK_COMB (@lem6988126 A f s g) (@lem6988127 A x s)). Qed.
Lemma lem6988129 {A : Type'} (x : type684 A) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term170 A f g x s) = (term171 A x f s g).
Proof. exact (eq_refl (term170 A f g x s)). Qed.
Lemma lem6988130 {A : Type'} (x : type684 A) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term169 A f g x s) = (term171 A x f s g).
Proof. exact (TRANS (@lem6988128 A f g x s) (@lem6988129 A x f s g)). Qed.
Lemma lem6988131 {A : Type'} (x : type684 A) (f : A -> nat) (g : A -> nat) : (term172 A f g x) = (term173 A x f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6988130 A x f s g)). Qed.
Lemma lem6988132 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6988133 {A : Type'} (x : type684 A) (f : A -> nat) (g : A -> nat) : (term174 A f g x) = (term175 A x f g).
Proof. exact (MK_COMB (@lem6988132 A) (@lem6988131 A x f g)). Qed.
Lemma lem6988134 {A : Type'} (f : A -> nat) (g : A -> nat) : (term176 A f g) = (term177 A f g).
Proof. exact (fun_ext (fun x : type684 A => @lem6988133 A x f g)). Qed.
Lemma lem6988135 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem6988136 {A : Type'} (f : A -> nat) (g : A -> nat) : (term159 A f g) = (term178 A f g).
Proof. exact (MK_COMB (@lem6988135 A) (@lem6988134 A f g)). Qed.
Lemma lem6988137 {A : Type'} (f : A -> nat) (g : A -> nat) : ((term158 A f g) = (term159 A f g)) = ((term153 A f g) = (term178 A f g)).
Proof. exact (MK_COMB (@lem6988125 A f g) (@lem6988136 A f g)). Qed.
Lemma lem6988138 {A : Type'} (f : A -> nat) (g : A -> nat) : (term153 A f g) = (term178 A f g).
Proof. exact (EQ_MP (@lem6988137 A f g) (@lem6988112 A f g)). Qed.
Lemma lem6988139 {A : Type'} (f : A -> nat) (g : A -> nat) : (term130 A f g) = (term178 A f g).
Proof. exact (TRANS (@lem6988108 A f g) (@lem6988138 A f g)). Qed.
Lemma lem6988140 {A : Type'} (f : A -> nat) : (term131 A f) = (term179 A f).
Proof. exact (fun_ext (fun g : A -> nat => @lem6988139 A f g)). Qed.
Lemma lem6988141 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6988142 {A : Type'} (f : A -> nat) : (term132 A f) = (term180 A f).
Proof. exact (MK_COMB (@lem6988141 A) (@lem6988140 A f)). Qed.
Lemma lem6988144 {A B : Type'} (P : type1413 A B) : (term154 A B P) = (term155 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6988145 {A : Type'} (P : type690 A) : (term181 A P) = (term182 A P).
Proof. exact (@lem6988144 (A -> nat) (type684 A) P). Qed.
Lemma lem6988146 {A : Type'} (f : A -> nat) : (term183 A f) = (term184 A f).
Proof. exact (@lem6988145 A (term185 A f)). Qed.
Lemma lem6988147 {A : Type'} (f : A -> nat) (g : A -> nat) : (term186 A f g) = (term177 A f g).
Proof. exact (eq_refl (term186 A f g)). Qed.
Lemma lem6988148 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6988149 {A : Type'} (f : A -> nat) (g : A -> nat) (x : type684 A) : (term187 A f g x) = (term188 A f g x).
Proof. exact (MK_COMB (@lem6988147 A f g) (@lem6988148 A x)). Qed.
Lemma lem6988150 {A : Type'} (x : type684 A) (f : A -> nat) (g : A -> nat) : (term188 A f g x) = (term175 A x f g).
Proof. exact (eq_refl (term188 A f g x)). Qed.
Lemma lem6988151 {A : Type'} (x : type684 A) (f : A -> nat) (g : A -> nat) : (term187 A f g x) = (term175 A x f g).
Proof. exact (TRANS (@lem6988149 A f g x) (@lem6988150 A x f g)). Qed.
Lemma lem6988152 {A : Type'} (f : A -> nat) (g : A -> nat) : (term189 A f g) = (term177 A f g).
Proof. exact (fun_ext (fun x : type684 A => @lem6988151 A x f g)). Qed.
Lemma lem6988153 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem6988154 {A : Type'} (f : A -> nat) (g : A -> nat) : (term190 A f g) = (term178 A f g).
Proof. exact (MK_COMB (@lem6988153 A) (@lem6988152 A f g)). Qed.
Lemma lem6988155 {A : Type'} (f : A -> nat) : (term191 A f) = (term179 A f).
Proof. exact (fun_ext (fun g : A -> nat => @lem6988154 A f g)). Qed.
Lemma lem6988156 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6988157 {A : Type'} (f : A -> nat) : (term183 A f) = (term180 A f).
Proof. exact (MK_COMB (@lem6988156 A) (@lem6988155 A f)). Qed.
Lemma lem6988158 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6988159 {A : Type'} (f : A -> nat) : (term192 A f) = (term193 A f).
Proof. exact (MK_COMB (@lem6988158) (@lem6988157 A f)). Qed.
Lemma lem6988160 {A : Type'} (f : A -> nat) (g : A -> nat) : (term186 A f g) = (term177 A f g).
Proof. exact (eq_refl (term186 A f g)). Qed.
Lemma lem6988161 {A : Type'} (x : type694 A) (g : A -> nat) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem6988162 {A : Type'} (f : A -> nat) (x : type694 A) (g : A -> nat) : (term194 A f x g) = (term195 A f x g).
Proof. exact (MK_COMB (@lem6988160 A f g) (@lem6988161 A x g)). Qed.
Lemma lem6988163 {A : Type'} (x : type694 A) (f : A -> nat) (g : A -> nat) : (term195 A f x g) = (term196 A x f g).
Proof. exact (eq_refl (term195 A f x g)). Qed.
Lemma lem6988164 {A : Type'} (x : type694 A) (f : A -> nat) (g : A -> nat) : (term194 A f x g) = (term196 A x f g).
Proof. exact (TRANS (@lem6988162 A f x g) (@lem6988163 A x f g)). Qed.
Lemma lem6988165 {A : Type'} (x : type694 A) (f : A -> nat) : (term197 A f x) = (term198 A x f).
Proof. exact (fun_ext (fun g : A -> nat => @lem6988164 A x f g)). Qed.
Lemma lem6988166 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6988167 {A : Type'} (x : type694 A) (f : A -> nat) : (term199 A f x) = (term200 A x f).
Proof. exact (MK_COMB (@lem6988166 A) (@lem6988165 A x f)). Qed.
Lemma lem6988168 {A : Type'} (f : A -> nat) : (term201 A f) = (term202 A f).
Proof. exact (fun_ext (fun x : type694 A => @lem6988167 A x f)). Qed.
Lemma lem6988169 {A : Type'} : (@ex ((A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem6988170 {A : Type'} (f : A -> nat) : (term184 A f) = (term203 A f).
Proof. exact (MK_COMB (@lem6988169 A) (@lem6988168 A f)). Qed.
Lemma lem6988171 {A : Type'} (f : A -> nat) : ((term183 A f) = (term184 A f)) = ((term180 A f) = (term203 A f)).
Proof. exact (MK_COMB (@lem6988159 A f) (@lem6988170 A f)). Qed.
Lemma lem6988172 {A : Type'} (f : A -> nat) : (term180 A f) = (term203 A f).
Proof. exact (EQ_MP (@lem6988171 A f) (@lem6988146 A f)). Qed.
Lemma lem6988173 {A : Type'} (f : A -> nat) : (term132 A f) = (term203 A f).
Proof. exact (TRANS (@lem6988142 A f) (@lem6988172 A f)). Qed.
Lemma lem6988174 {A : Type'} : (term133 A) = (term204 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6988173 A f)). Qed.
Lemma lem6988175 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6988176 {A : Type'} : (term134 A) = (term205 A).
Proof. exact (MK_COMB (@lem6988175 A) (@lem6988174 A)). Qed.
Lemma lem6988178 {A B : Type'} (P : type1413 A B) : (term154 A B P) = (term155 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6988179 {A : Type'} (P : type691 A) : (term206 A P) = (term207 A P).
Proof. exact (@lem6988178 (A -> nat) (type694 A) P). Qed.
Lemma lem6988180 {A : Type'} : (term208 A) = (term209 A).
Proof. exact (@lem6988179 A (term210 A)). Qed.
Lemma lem6988181 {A : Type'} (f : A -> nat) : (term211 A f) = (term202 A f).
Proof. exact (eq_refl (term211 A f)). Qed.
Lemma lem6988182 {A : Type'} (x : type694 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6988183 {A : Type'} (f : A -> nat) (x : type694 A) : (term212 A f x) = (term213 A f x).
Proof. exact (MK_COMB (@lem6988181 A f) (@lem6988182 A x)). Qed.
Lemma lem6988184 {A : Type'} (x : type694 A) (f : A -> nat) : (term213 A f x) = (term200 A x f).
Proof. exact (eq_refl (term213 A f x)). Qed.
Lemma lem6988185 {A : Type'} (x : type694 A) (f : A -> nat) : (term212 A f x) = (term200 A x f).
Proof. exact (TRANS (@lem6988183 A f x) (@lem6988184 A x f)). Qed.
Lemma lem6988186 {A : Type'} (f : A -> nat) : (term214 A f) = (term202 A f).
Proof. exact (fun_ext (fun x : type694 A => @lem6988185 A x f)). Qed.
Lemma lem6988187 {A : Type'} : (@ex ((A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem6988188 {A : Type'} (f : A -> nat) : (term215 A f) = (term203 A f).
Proof. exact (MK_COMB (@lem6988187 A) (@lem6988186 A f)). Qed.
Lemma lem6988189 {A : Type'} : (term216 A) = (term204 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6988188 A f)). Qed.
Lemma lem6988190 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6988191 {A : Type'} : (term208 A) = (term205 A).
Proof. exact (MK_COMB (@lem6988190 A) (@lem6988189 A)). Qed.
Lemma lem6988192 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6988193 {A : Type'} : (term217 A) = (term218 A).
Proof. exact (MK_COMB (@lem6988192) (@lem6988191 A)). Qed.
Lemma lem6988194 {A : Type'} (f : A -> nat) : (term211 A f) = (term202 A f).
Proof. exact (eq_refl (term211 A f)). Qed.
Lemma lem6988195 {A : Type'} (x : type695 A) (f : A -> nat) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem6988196 {A : Type'} (x : type695 A) (f : A -> nat) : (term219 A x f) = (term220 A x f).
Proof. exact (MK_COMB (@lem6988194 A f) (@lem6988195 A x f)). Qed.
Lemma lem6988197 {A : Type'} (x : type695 A) (f : A -> nat) : (term220 A x f) = (term221 A x f).
Proof. exact (eq_refl (term220 A x f)). Qed.
Lemma lem6988198 {A : Type'} (x : type695 A) (f : A -> nat) : (term219 A x f) = (term221 A x f).
Proof. exact (TRANS (@lem6988196 A x f) (@lem6988197 A x f)). Qed.
Lemma lem6988199 {A : Type'} (x : type695 A) : (term222 A x) = (term223 A x).
Proof. exact (fun_ext (fun f : A -> nat => @lem6988198 A x f)). Qed.
Lemma lem6988200 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6988201 {A : Type'} (x : type695 A) : (term224 A x) = (term225 A x).
Proof. exact (MK_COMB (@lem6988200 A) (@lem6988199 A x)). Qed.
Lemma lem6988202 {A : Type'} : (term226 A) = (term227 A).
Proof. exact (fun_ext (fun x : type695 A => @lem6988201 A x)). Qed.
Lemma lem6988203 {A : Type'} : (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem6988204 {A : Type'} : (term209 A) = (term228 A).
Proof. exact (MK_COMB (@lem6988203 A) (@lem6988202 A)). Qed.
Lemma lem6988205 {A : Type'} : ((term208 A) = (term209 A)) = ((term205 A) = (term228 A)).
Proof. exact (MK_COMB (@lem6988193 A) (@lem6988204 A)). Qed.
Lemma lem6988206 {A : Type'} : (term205 A) = (term228 A).
Proof. exact (EQ_MP (@lem6988205 A) (@lem6988180 A)). Qed.
Lemma lem6988208 {A : Type'} : (term134 A) = (term228 A).
Proof. exact (TRANS (@lem6988176 A) (@lem6988206 A)). Qed.
Lemma lem6988209 {A : Type'} : (term12 A) = (term228 A).
Proof. exact (TRANS (@lem6987976 A) (@lem6988208 A)). Qed.
Lemma lem6988210 {A : Type'} (h1 : term12 A) : term228 A.
Proof. exact (EQ_MP (@lem6988209 A) (@lem6987445 A h1)). Qed.
Lemma lem6988222 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term229 A v u f x) = (term230 A v u f x).
Proof. exact (@lem17362 (term77 A v x u) ((f x) = (NUMERAL 0))). Qed.
Lemma lem6988223 {A : Type'} (P : A -> Prop) : (term116 A P) = (term117 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6988224 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term231 A v u f) = (term232 A v u f).
Proof. exact (@lem6988223 A (term31 A v u f)). Qed.
Lemma lem6988225 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term233 A v u f x) = (term30 A v u f x).
Proof. exact (eq_refl (term233 A v u f x)). Qed.
Lemma lem6988226 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6988227 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term234 A v u f x) = (term229 A v u f x).
Proof. exact (MK_COMB (@lem6988226) (@lem6988225 A v u f x)). Qed.
Lemma lem6988228 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term234 A v u f x) = (term230 A v u f x).
Proof. exact (TRANS (@lem6988227 A v u f x) (@lem6988222 A v u f x)). Qed.
Lemma lem6988229 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term235 A v u f) = (term236 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6988228 A v u f x)). Qed.
Lemma lem6988230 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6988231 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term232 A v u f) = (term237 A v u f).
Proof. exact (MK_COMB (@lem6988230 A) (@lem6988229 A v u f)). Qed.
Lemma lem6988232 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term231 A v u f) = (term237 A v u f).
Proof. exact (TRANS (@lem6988224 A v u f) (@lem6988231 A v u f)). Qed.
Lemma lem6988234 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term238 A u v) = (term238 A u v).
Proof. exact (eq_refl (term238 A u v)). Qed.
Lemma lem6988235 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term239 A v u f) = (term240 A v u f).
Proof. exact (MK_COMB (@lem6988234 A u v) (@lem6988232 A v u f)). Qed.
Lemma lem6988236 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term241 A v u f) = (term239 A v u f).
Proof. exact (@lem17045 (@SUBSET A u v) (term32 A v u f)). Qed.
Lemma lem6988237 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term241 A v u f) = (term240 A v u f).
Proof. exact (TRANS (@lem6988236 A v u f) (@lem6988235 A v u f)). Qed.
Lemma lem6988238 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((@nsum A v f) = (@nsum A u f)) = ((@nsum A v f) = (@nsum A u f)).
Proof. exact (eq_refl ((@nsum A v f) = (@nsum A u f))). Qed.
Lemma lem6988239 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6988240 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term242 A v u f) = (term243 A v u f).
Proof. exact (MK_COMB (@lem6988239) (@lem6988237 A v u f)). Qed.
Lemma lem6988241 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term244 A v u f) = (term245 A v u f).
Proof. exact (MK_COMB (@lem6988240 A v u f) (@lem6988238 A v u f)). Qed.
Lemma lem6988242 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term36 A v u f) = (term244 A v u f).
Proof. exact (@lem17265 (term34 A v u f) ((@nsum A v f) = (@nsum A u f))). Qed.
Lemma lem6988243 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term36 A v u f) = (term245 A v u f).
Proof. exact (TRANS (@lem6988242 A v u f) (@lem6988241 A v u f)). Qed.
Lemma lem6988244 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term37 A u f) = (term246 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6988243 A v u f)). Qed.
Lemma lem6988245 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6988246 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term38 A u f) = (term247 A u f).
Proof. exact (MK_COMB (@lem6988245 A) (@lem6988244 A u f)). Qed.
Lemma lem6988247 {A : Type'} (f : A -> nat) : (term39 A f) = (term248 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6988246 A u f)). Qed.
Lemma lem6988248 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6988249 {A : Type'} (f : A -> nat) : (term40 A f) = (term249 A f).
Proof. exact (MK_COMB (@lem6988248 A) (@lem6988247 A f)). Qed.
Lemma lem6988250 {A : Type'} : (term41 A) = (term250 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6988249 A f)). Qed.
Lemma lem6988251 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6988252 {A : Type'} : (term11 A) = (term251 A).
Proof. exact (MK_COMB (@lem6988251 A) (@lem6988250 A)). Qed.
Lemma lem6988359 {A : Type'} (P : Prop) (Q : A -> Prop) : (term252 A P Q) = (term253 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6988360 {A : Type'} (P : Prop) (Q : A -> Prop) : (term252 A P Q) = (term253 A P Q).
Proof. exact (@lem6988359 A P Q). Qed.
Lemma lem6988361 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term254 A v u f) = (term255 A v u f).
Proof. exact (@lem6988360 A (term256 A u v) (term236 A v u f)). Qed.
Lemma lem6988362 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term257 A v u f x) = (term230 A v u f x).
Proof. exact (eq_refl (term257 A v u f x)). Qed.
Lemma lem6988363 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term258 A v u f) = (term236 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6988362 A v u f x)). Qed.
Lemma lem6988364 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6988365 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term259 A v u f) = (term237 A v u f).
Proof. exact (MK_COMB (@lem6988364 A) (@lem6988363 A v u f)). Qed.
Lemma lem6988366 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term238 A u v) = (term238 A u v).
Proof. exact (eq_refl (term238 A u v)). Qed.
Lemma lem6988367 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term254 A v u f) = (term240 A v u f).
Proof. exact (MK_COMB (@lem6988366 A u v) (@lem6988365 A v u f)). Qed.
Lemma lem6988368 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6988369 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term260 A v u f) = (term261 A v u f).
Proof. exact (MK_COMB (@lem6988368) (@lem6988367 A v u f)). Qed.
Lemma lem6988370 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term257 A v u f x) = (term230 A v u f x).
Proof. exact (eq_refl (term257 A v u f x)). Qed.
Lemma lem6988371 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term238 A u v) = (term238 A u v).
Proof. exact (eq_refl (term238 A u v)). Qed.
Lemma lem6988372 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term262 A v u f x) = (term263 A v u f x).
Proof. exact (MK_COMB (@lem6988371 A u v) (@lem6988370 A v u f x)). Qed.
Lemma lem6988373 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term264 A v u f) = (term265 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6988372 A v u f x)). Qed.
Lemma lem6988374 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6988375 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term255 A v u f) = (term266 A v u f).
Proof. exact (MK_COMB (@lem6988374 A) (@lem6988373 A v u f)). Qed.
Lemma lem6988376 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term254 A v u f) = (term255 A v u f)) = ((term240 A v u f) = (term266 A v u f)).
Proof. exact (MK_COMB (@lem6988369 A v u f) (@lem6988375 A v u f)). Qed.
Lemma lem6988377 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term240 A v u f) = (term266 A v u f).
Proof. exact (EQ_MP (@lem6988376 A v u f) (@lem6988361 A v u f)). Qed.
Lemma lem6988378 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6988379 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term243 A v u f) = (term267 A v u f).
Proof. exact (MK_COMB (@lem6988378) (@lem6988377 A v u f)). Qed.
Lemma lem6988380 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((@nsum A v f) = (@nsum A u f)) = ((@nsum A v f) = (@nsum A u f)).
Proof. exact (eq_refl ((@nsum A v f) = (@nsum A u f))). Qed.
Lemma lem6988381 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term245 A v u f) = (term268 A v u f).
Proof. exact (MK_COMB (@lem6988379 A v u f) (@lem6988380 A v u f)). Qed.
Lemma lem6988383 {A : Type'} (P : A -> Prop) (Q : Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6988384 {A : Type'} (P : A -> Prop) (Q : Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (@lem6988383 A P Q). Qed.
Lemma lem6988385 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term269 A v u f) = (term270 A v u f).
Proof. exact (@lem6988384 A (term265 A v u f) ((@nsum A v f) = (@nsum A u f))). Qed.
Lemma lem6988386 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term271 A v u f x) = (term263 A v u f x).
Proof. exact (eq_refl (term271 A v u f x)). Qed.
Lemma lem6988387 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term272 A v u f) = (term265 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6988386 A v u f x)). Qed.
Lemma lem6988388 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6988389 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term273 A v u f) = (term266 A v u f).
Proof. exact (MK_COMB (@lem6988388 A) (@lem6988387 A v u f)). Qed.
Lemma lem6988390 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6988391 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term274 A v u f) = (term267 A v u f).
Proof. exact (MK_COMB (@lem6988390) (@lem6988389 A v u f)). Qed.
Lemma lem6988392 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((@nsum A v f) = (@nsum A u f)) = ((@nsum A v f) = (@nsum A u f)).
Proof. exact (eq_refl ((@nsum A v f) = (@nsum A u f))). Qed.
Lemma lem6988393 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term269 A v u f) = (term268 A v u f).
Proof. exact (MK_COMB (@lem6988391 A v u f) (@lem6988392 A v u f)). Qed.
Lemma lem6988394 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6988395 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term275 A v u f) = (term276 A v u f).
Proof. exact (MK_COMB (@lem6988394) (@lem6988393 A v u f)). Qed.
Lemma lem6988396 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term271 A v u f x) = (term263 A v u f x).
Proof. exact (eq_refl (term271 A v u f x)). Qed.
Lemma lem6988397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6988398 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term277 A v u f x) = (term278 A v u f x).
Proof. exact (MK_COMB (@lem6988397) (@lem6988396 A v u f x)). Qed.
Lemma lem6988399 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((@nsum A v f) = (@nsum A u f)) = ((@nsum A v f) = (@nsum A u f)).
Proof. exact (eq_refl ((@nsum A v f) = (@nsum A u f))). Qed.
Lemma lem6988400 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term279 A x v u f) = (term280 A x v u f).
Proof. exact (MK_COMB (@lem6988398 A v u f x) (@lem6988399 A v u f)). Qed.
Lemma lem6988401 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term281 A v u f) = (term282 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6988400 A x v u f)). Qed.
Lemma lem6988402 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6988403 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term270 A v u f) = (term283 A v u f).
Proof. exact (MK_COMB (@lem6988402 A) (@lem6988401 A v u f)). Qed.
Lemma lem6988404 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term269 A v u f) = (term270 A v u f)) = ((term268 A v u f) = (term283 A v u f)).
Proof. exact (MK_COMB (@lem6988395 A v u f) (@lem6988403 A v u f)). Qed.
Lemma lem6988405 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term268 A v u f) = (term283 A v u f).
Proof. exact (EQ_MP (@lem6988404 A v u f) (@lem6988385 A v u f)). Qed.
Lemma lem6988406 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term245 A v u f) = (term283 A v u f).
Proof. exact (TRANS (@lem6988381 A v u f) (@lem6988405 A v u f)). Qed.
Lemma lem6988407 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term246 A u f) = (term284 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6988406 A v u f)). Qed.
Lemma lem6988408 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6988409 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term247 A u f) = (term285 A u f).
Proof. exact (MK_COMB (@lem6988408 A) (@lem6988407 A u f)). Qed.
Lemma lem6988411 {A B : Type'} (P : type1413 A B) : (term154 A B P) = (term155 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6988412 {A : Type'} (P : type672 A) : (term156 A P) = (term157 A P).
Proof. exact (@lem6988411 (A -> Prop) A P). Qed.
Lemma lem6988413 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term286 A u f) = (term287 A u f).
Proof. exact (@lem6988412 A (term288 A u f)). Qed.
Lemma lem6988414 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term289 A u f v) = (term282 A v u f).
Proof. exact (eq_refl (term289 A u f v)). Qed.
Lemma lem6988415 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6988416 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term290 A u f v x) = (term291 A v u f x).
Proof. exact (MK_COMB (@lem6988414 A v u f) (@lem6988415 A x)). Qed.
Lemma lem6988417 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term291 A v u f x) = (term280 A x v u f).
Proof. exact (eq_refl (term291 A v u f x)). Qed.
Lemma lem6988418 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term290 A u f v x) = (term280 A x v u f).
Proof. exact (TRANS (@lem6988416 A v u f x) (@lem6988417 A x v u f)). Qed.
Lemma lem6988419 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term292 A u f v) = (term282 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6988418 A x v u f)). Qed.
Lemma lem6988420 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6988421 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term293 A u f v) = (term283 A v u f).
Proof. exact (MK_COMB (@lem6988420 A) (@lem6988419 A v u f)). Qed.
Lemma lem6988422 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term294 A u f) = (term284 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6988421 A v u f)). Qed.
Lemma lem6988423 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6988424 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term286 A u f) = (term285 A u f).
Proof. exact (MK_COMB (@lem6988423 A) (@lem6988422 A u f)). Qed.
Lemma lem6988425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6988426 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term295 A u f) = (term296 A u f).
Proof. exact (MK_COMB (@lem6988425) (@lem6988424 A u f)). Qed.
Lemma lem6988427 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term289 A u f v) = (term282 A v u f).
Proof. exact (eq_refl (term289 A u f v)). Qed.
Lemma lem6988428 {A : Type'} (x : type684 A) (v : A -> Prop) : (x v) = (x v).
Proof. exact (eq_refl (x v)). Qed.
Lemma lem6988429 {A : Type'} (u : A -> Prop) (f : A -> nat) (x : type684 A) (v : A -> Prop) : (term297 A u f x v) = (term298 A u f x v).
Proof. exact (MK_COMB (@lem6988427 A v u f) (@lem6988428 A x v)). Qed.
Lemma lem6988430 {A : Type'} (x : type684 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term298 A u f x v) = (term299 A x v u f).
Proof. exact (eq_refl (term298 A u f x v)). Qed.
Lemma lem6988431 {A : Type'} (x : type684 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term297 A u f x v) = (term299 A x v u f).
Proof. exact (TRANS (@lem6988429 A u f x v) (@lem6988430 A x v u f)). Qed.
Lemma lem6988432 {A : Type'} (x : type684 A) (u : A -> Prop) (f : A -> nat) : (term300 A u f x) = (term301 A x u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6988431 A x v u f)). Qed.
Lemma lem6988433 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6988434 {A : Type'} (x : type684 A) (u : A -> Prop) (f : A -> nat) : (term302 A u f x) = (term303 A x u f).
Proof. exact (MK_COMB (@lem6988433 A) (@lem6988432 A x u f)). Qed.
Lemma lem6988435 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term304 A u f) = (term305 A u f).
Proof. exact (fun_ext (fun x : type684 A => @lem6988434 A x u f)). Qed.
Lemma lem6988436 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem6988437 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term287 A u f) = (term306 A u f).
Proof. exact (MK_COMB (@lem6988436 A) (@lem6988435 A u f)). Qed.
Lemma lem6988438 {A : Type'} (u : A -> Prop) (f : A -> nat) : ((term286 A u f) = (term287 A u f)) = ((term285 A u f) = (term306 A u f)).
Proof. exact (MK_COMB (@lem6988426 A u f) (@lem6988437 A u f)). Qed.
Lemma lem6988439 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term285 A u f) = (term306 A u f).
Proof. exact (EQ_MP (@lem6988438 A u f) (@lem6988413 A u f)). Qed.
Lemma lem6988440 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term247 A u f) = (term306 A u f).
Proof. exact (TRANS (@lem6988409 A u f) (@lem6988439 A u f)). Qed.
Lemma lem6988441 {A : Type'} (f : A -> nat) : (term248 A f) = (term307 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6988440 A u f)). Qed.
Lemma lem6988442 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6988443 {A : Type'} (f : A -> nat) : (term249 A f) = (term308 A f).
Proof. exact (MK_COMB (@lem6988442 A) (@lem6988441 A f)). Qed.
Lemma lem6988445 {A B : Type'} (P : type1413 A B) : (term154 A B P) = (term155 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6988446 {A : Type'} (P : type597 A) : (term309 A P) = (term310 A P).
Proof. exact (@lem6988445 (A -> Prop) (type684 A) P). Qed.
Lemma lem6988447 {A : Type'} (f : A -> nat) : (term311 A f) = (term312 A f).
Proof. exact (@lem6988446 A (term313 A f)). Qed.
Lemma lem6988448 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term314 A f u) = (term305 A u f).
Proof. exact (eq_refl (term314 A f u)). Qed.
Lemma lem6988449 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6988450 {A : Type'} (u : A -> Prop) (f : A -> nat) (x : type684 A) : (term315 A f u x) = (term316 A u f x).
Proof. exact (MK_COMB (@lem6988448 A u f) (@lem6988449 A x)). Qed.
Lemma lem6988451 {A : Type'} (x : type684 A) (u : A -> Prop) (f : A -> nat) : (term316 A u f x) = (term303 A x u f).
Proof. exact (eq_refl (term316 A u f x)). Qed.
Lemma lem6988452 {A : Type'} (x : type684 A) (u : A -> Prop) (f : A -> nat) : (term315 A f u x) = (term303 A x u f).
Proof. exact (TRANS (@lem6988450 A u f x) (@lem6988451 A x u f)). Qed.
Lemma lem6988453 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term317 A f u) = (term305 A u f).
Proof. exact (fun_ext (fun x : type684 A => @lem6988452 A x u f)). Qed.
Lemma lem6988454 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem6988455 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term318 A f u) = (term306 A u f).
Proof. exact (MK_COMB (@lem6988454 A) (@lem6988453 A u f)). Qed.
Lemma lem6988456 {A : Type'} (f : A -> nat) : (term319 A f) = (term307 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6988455 A u f)). Qed.
Lemma lem6988457 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6988458 {A : Type'} (f : A -> nat) : (term311 A f) = (term308 A f).
Proof. exact (MK_COMB (@lem6988457 A) (@lem6988456 A f)). Qed.
Lemma lem6988459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6988460 {A : Type'} (f : A -> nat) : (term320 A f) = (term321 A f).
Proof. exact (MK_COMB (@lem6988459) (@lem6988458 A f)). Qed.
Lemma lem6988461 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term314 A f u) = (term305 A u f).
Proof. exact (eq_refl (term314 A f u)). Qed.
Lemma lem6988462 {A : Type'} (x : type638 A) (u : A -> Prop) : (x u) = (x u).
Proof. exact (eq_refl (x u)). Qed.
Lemma lem6988463 {A : Type'} (f : A -> nat) (x : type638 A) (u : A -> Prop) : (term322 A f x u) = (term323 A f x u).
Proof. exact (MK_COMB (@lem6988461 A u f) (@lem6988462 A x u)). Qed.
Lemma lem6988464 {A : Type'} (x : type638 A) (u : A -> Prop) (f : A -> nat) : (term323 A f x u) = (term324 A x u f).
Proof. exact (eq_refl (term323 A f x u)). Qed.
Lemma lem6988465 {A : Type'} (x : type638 A) (u : A -> Prop) (f : A -> nat) : (term322 A f x u) = (term324 A x u f).
Proof. exact (TRANS (@lem6988463 A f x u) (@lem6988464 A x u f)). Qed.
Lemma lem6988466 {A : Type'} (x : type638 A) (f : A -> nat) : (term325 A f x) = (term326 A x f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6988465 A x u f)). Qed.
Lemma lem6988467 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6988468 {A : Type'} (x : type638 A) (f : A -> nat) : (term327 A f x) = (term328 A x f).
Proof. exact (MK_COMB (@lem6988467 A) (@lem6988466 A x f)). Qed.
Lemma lem6988469 {A : Type'} (f : A -> nat) : (term329 A f) = (term330 A f).
Proof. exact (fun_ext (fun x : type638 A => @lem6988468 A x f)). Qed.
Lemma lem6988470 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem6988471 {A : Type'} (f : A -> nat) : (term312 A f) = (term331 A f).
Proof. exact (MK_COMB (@lem6988470 A) (@lem6988469 A f)). Qed.
Lemma lem6988472 {A : Type'} (f : A -> nat) : ((term311 A f) = (term312 A f)) = ((term308 A f) = (term331 A f)).
Proof. exact (MK_COMB (@lem6988460 A f) (@lem6988471 A f)). Qed.
Lemma lem6988473 {A : Type'} (f : A -> nat) : (term308 A f) = (term331 A f).
Proof. exact (EQ_MP (@lem6988472 A f) (@lem6988447 A f)). Qed.
Lemma lem6988474 {A : Type'} (f : A -> nat) : (term249 A f) = (term331 A f).
Proof. exact (TRANS (@lem6988443 A f) (@lem6988473 A f)). Qed.
Lemma lem6988475 {A : Type'} : (term250 A) = (term332 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6988474 A f)). Qed.
Lemma lem6988476 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6988477 {A : Type'} : (term251 A) = (term333 A).
Proof. exact (MK_COMB (@lem6988476 A) (@lem6988475 A)). Qed.
Lemma lem6988479 {A B : Type'} (P : type1413 A B) : (term154 A B P) = (term155 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6988480 {A : Type'} (P : type689 A) : (term334 A P) = (term335 A P).
Proof. exact (@lem6988479 (A -> nat) (type638 A) P). Qed.
Lemma lem6988481 {A : Type'} : (term336 A) = (term337 A).
Proof. exact (@lem6988480 A (term338 A)). Qed.
Lemma lem6988482 {A : Type'} (f : A -> nat) : (term339 A f) = (term330 A f).
Proof. exact (eq_refl (term339 A f)). Qed.
Lemma lem6988483 {A : Type'} (x : type638 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6988484 {A : Type'} (f : A -> nat) (x : type638 A) : (term340 A f x) = (term341 A f x).
Proof. exact (MK_COMB (@lem6988482 A f) (@lem6988483 A x)). Qed.
Lemma lem6988485 {A : Type'} (x : type638 A) (f : A -> nat) : (term341 A f x) = (term328 A x f).
Proof. exact (eq_refl (term341 A f x)). Qed.
Lemma lem6988486 {A : Type'} (x : type638 A) (f : A -> nat) : (term340 A f x) = (term328 A x f).
Proof. exact (TRANS (@lem6988484 A f x) (@lem6988485 A x f)). Qed.
Lemma lem6988487 {A : Type'} (f : A -> nat) : (term342 A f) = (term330 A f).
Proof. exact (fun_ext (fun x : type638 A => @lem6988486 A x f)). Qed.
Lemma lem6988488 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem6988489 {A : Type'} (f : A -> nat) : (term343 A f) = (term331 A f).
Proof. exact (MK_COMB (@lem6988488 A) (@lem6988487 A f)). Qed.
Lemma lem6988490 {A : Type'} : (term344 A) = (term332 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6988489 A f)). Qed.
Lemma lem6988491 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6988492 {A : Type'} : (term336 A) = (term333 A).
Proof. exact (MK_COMB (@lem6988491 A) (@lem6988490 A)). Qed.
Lemma lem6988493 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6988494 {A : Type'} : (term345 A) = (term346 A).
Proof. exact (MK_COMB (@lem6988493) (@lem6988492 A)). Qed.
Lemma lem6988495 {A : Type'} (f : A -> nat) : (term339 A f) = (term330 A f).
Proof. exact (eq_refl (term339 A f)). Qed.
Lemma lem6988496 {A : Type'} (x : type693 A) (f : A -> nat) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem6988497 {A : Type'} (x : type693 A) (f : A -> nat) : (term347 A x f) = (term348 A x f).
Proof. exact (MK_COMB (@lem6988495 A f) (@lem6988496 A x f)). Qed.
Lemma lem6988498 {A : Type'} (x : type693 A) (f : A -> nat) : (term348 A x f) = (term349 A x f).
Proof. exact (eq_refl (term348 A x f)). Qed.
Lemma lem6988499 {A : Type'} (x : type693 A) (f : A -> nat) : (term347 A x f) = (term349 A x f).
Proof. exact (TRANS (@lem6988497 A x f) (@lem6988498 A x f)). Qed.
Lemma lem6988500 {A : Type'} (x : type693 A) : (term350 A x) = (term351 A x).
Proof. exact (fun_ext (fun f : A -> nat => @lem6988499 A x f)). Qed.
Lemma lem6988501 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6988502 {A : Type'} (x : type693 A) : (term352 A x) = (term353 A x).
Proof. exact (MK_COMB (@lem6988501 A) (@lem6988500 A x)). Qed.
Lemma lem6988503 {A : Type'} : (term354 A) = (term355 A).
Proof. exact (fun_ext (fun x : type693 A => @lem6988502 A x)). Qed.
Lemma lem6988504 {A : Type'} : (@ex ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem6988505 {A : Type'} : (term337 A) = (term356 A).
Proof. exact (MK_COMB (@lem6988504 A) (@lem6988503 A)). Qed.
Lemma lem6988506 {A : Type'} : ((term336 A) = (term337 A)) = ((term333 A) = (term356 A)).
Proof. exact (MK_COMB (@lem6988494 A) (@lem6988505 A)). Qed.
Lemma lem6988507 {A : Type'} : (term333 A) = (term356 A).
Proof. exact (EQ_MP (@lem6988506 A) (@lem6988481 A)). Qed.
Lemma lem6988509 {A : Type'} : (term251 A) = (term356 A).
Proof. exact (TRANS (@lem6988477 A) (@lem6988507 A)). Qed.
Lemma lem6988510 {A : Type'} : (term11 A) = (term356 A).
Proof. exact (TRANS (@lem6988252 A) (@lem6988509 A)). Qed.
Lemma lem6988511 {A : Type'} (h1 : term11 A) : term356 A.
Proof. exact (EQ_MP (@lem6988510 A) (@lem6987446 A h1)). Qed.
Lemma lem6988512 {A : Type'} (x : type693 A) (h1 : term353 A x) : term353 A x.
Proof. exact (h1). Qed.
Lemma lem6988513 {A : Type'} (x' : type695 A) (h1 : term225 A x') : term225 A x'.
Proof. exact (h1). Qed.
Lemma lem6988515 {A : Type'} (f : A -> nat) (g : A -> nat) (h1 : term105 A f g) : term105 A f g.
Proof. exact (h1). Qed.
Lemma lem6988516 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term98 A s f g) : term98 A s f g.
Proof. exact (h1). Qed.
Lemma lem6988517 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term88 A s f t g.
Proof. exact (h1). Qed.
Lemma lem6988518 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6988525 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988526 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem6988525 (A -> Prop) (type705 A) f x). Qed.
Lemma lem6988527 {A : Type'} (v : A -> Prop) : (@nsum A v) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) v).
Proof. exact (@lem6988526 A (@nsum A) v). Qed.
Lemma lem6988528 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6988529 {A : Type'} (v : A -> Prop) (f : A -> nat) : (@nsum A v f) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) v f).
Proof. exact (MK_COMB (@lem6988527 A v) (@lem6988528 A f)). Qed.
Lemma lem6988531 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988532 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem6988531 (A -> nat) nat f x). Qed.
Lemma lem6988533 {A : Type'} (v : A -> Prop) (f : A -> nat) : (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) v f) = (term357 A v f).
Proof. exact (@lem6988532 A (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) v) f). Qed.
Lemma lem6988535 {A : Type'} (v : A -> Prop) (f : A -> nat) : (@nsum A v f) = (term357 A v f).
Proof. exact (TRANS (@lem6988529 A v f) (@lem6988533 A v f)). Qed.
Lemma lem6988542 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988543 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem6988542 (A -> Prop) (type705 A) f x). Qed.
Lemma lem6988544 {A : Type'} (u : A -> Prop) : (@nsum A u) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) u).
Proof. exact (@lem6988543 A (@nsum A) u). Qed.
Lemma lem6988545 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6988546 {A : Type'} (u : A -> Prop) (f : A -> nat) : (@nsum A u f) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) u f).
Proof. exact (MK_COMB (@lem6988544 A u) (@lem6988545 A f)). Qed.
Lemma lem6988548 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988549 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem6988548 (A -> nat) nat f x). Qed.
Lemma lem6988550 {A : Type'} (u : A -> Prop) (f : A -> nat) : (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) u f) = (term357 A u f).
Proof. exact (@lem6988549 A (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) u) f). Qed.
Lemma lem6988552 {A : Type'} (u : A -> Prop) (f : A -> nat) : (@nsum A u f) = (term357 A u f).
Proof. exact (TRANS (@lem6988546 A u f) (@lem6988550 A u f)). Qed.
Lemma lem6988553 {A : Type'} (v : A -> Prop) (f : A -> nat) : (term358 A v f) = (term359 A v f).
Proof. exact (MK_COMB (@lem6988518) (@lem6988535 A v f)). Qed.
Lemma lem6988554 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((@nsum A v f) = (@nsum A u f)) = ((term357 A v f) = (term357 A u f)).
Proof. exact (MK_COMB (@lem6988553 A v f) (@lem6988552 A u f)). Qed.
Lemma lem6988555 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6988556 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6988557 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6988566 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988567 {A : Type'} (f : type693 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6988566 (A -> nat) (type638 A) f x). Qed.
Lemma lem6988568 {A : Type'} (x : type693 A) (f : A -> nat) : (x f) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f).
Proof. exact (@lem6988567 A x f). Qed.
Lemma lem6988569 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem6988570 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (x f u) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f u).
Proof. exact (MK_COMB (@lem6988568 A x f) (@lem6988569 A u)). Qed.
Lemma lem6988572 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988573 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6988572 (A -> Prop) (type684 A) f x). Qed.
Lemma lem6988574 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f u) = (term360 A x f u).
Proof. exact (@lem6988573 A (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f) u). Qed.
Lemma lem6988575 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (x f u) = (term360 A x f u).
Proof. exact (TRANS (@lem6988570 A x f u) (@lem6988574 A x f u)). Qed.
Lemma lem6988576 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem6988577 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term361 A x f u v).
Proof. exact (MK_COMB (@lem6988575 A x f u) (@lem6988576 A v)). Qed.
Lemma lem6988579 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988580 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem6988579 (A -> Prop) A f x). Qed.
Lemma lem6988581 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term361 A x f u v) = (term362 A x f u v).
Proof. exact (@lem6988580 A (term360 A x f u) v). Qed.
Lemma lem6988583 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term362 A x f u v).
Proof. exact (TRANS (@lem6988577 A x f u v) (@lem6988581 A x f u v)). Qed.
Lemma lem6988584 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term363 A x f u v) = (term364 A x f u v).
Proof. exact (MK_COMB (@lem6988557 A f) (@lem6988583 A x f u v)). Qed.
Lemma lem6988586 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988587 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem6988586 A nat f x). Qed.
Lemma lem6988588 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term364 A x f u v) = (term365 A x f u v).
Proof. exact (@lem6988587 A f (term362 A x f u v)). Qed.
Lemma lem6988589 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term363 A x f u v) = (term365 A x f u v).
Proof. exact (TRANS (@lem6988584 A x f u v) (@lem6988588 A x f u v)). Qed.
Lemma lem6988594 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988595 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem6988594 nat nat f x). Qed.
Lemma lem6988597 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem6988595 NUMERAL 0). Qed.
Lemma lem6988598 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term366 A x f u v) = (term367 A x f u v).
Proof. exact (MK_COMB (@lem6988556) (@lem6988589 A x f u v)). Qed.
Lemma lem6988599 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : ((term363 A x f u v) = (NUMERAL 0)) = ((term365 A x f u v) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (MK_COMB (@lem6988598 A x f u v) (@lem6988597)). Qed.
Lemma lem6988600 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term368 A x f u v) = (term369 A x f u v).
Proof. exact (MK_COMB (@lem6988555) (@lem6988599 A x f u v)). Qed.
Lemma lem6988601 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6988602 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem6988611 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988612 {A : Type'} (f : type693 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6988611 (A -> nat) (type638 A) f x). Qed.
Lemma lem6988613 {A : Type'} (x : type693 A) (f : A -> nat) : (x f) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f).
Proof. exact (@lem6988612 A x f). Qed.
Lemma lem6988614 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem6988615 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (x f u) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f u).
Proof. exact (MK_COMB (@lem6988613 A x f) (@lem6988614 A u)). Qed.
Lemma lem6988617 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988618 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6988617 (A -> Prop) (type684 A) f x). Qed.
Lemma lem6988619 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f u) = (term360 A x f u).
Proof. exact (@lem6988618 A (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f) u). Qed.
Lemma lem6988620 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (x f u) = (term360 A x f u).
Proof. exact (TRANS (@lem6988615 A x f u) (@lem6988619 A x f u)). Qed.
Lemma lem6988621 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem6988622 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term361 A x f u v).
Proof. exact (MK_COMB (@lem6988620 A x f u) (@lem6988621 A v)). Qed.
Lemma lem6988624 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988625 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem6988624 (A -> Prop) A f x). Qed.
Lemma lem6988626 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term361 A x f u v) = (term362 A x f u v).
Proof. exact (@lem6988625 A (term360 A x f u) v). Qed.
Lemma lem6988628 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term362 A x f u v).
Proof. exact (TRANS (@lem6988622 A x f u v) (@lem6988626 A x f u v)). Qed.
Lemma lem6988629 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem6988630 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term370 A x f u v) = (term371 A x f u v).
Proof. exact (MK_COMB (@lem6988602 A) (@lem6988628 A x f u v)). Qed.
Lemma lem6988631 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term372 A x f v u) = (term373 A x f v u).
Proof. exact (MK_COMB (@lem6988630 A x f u v) (@lem6988629 A u)). Qed.
Lemma lem6988633 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988634 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6988633 A (type686 A) f x). Qed.
Lemma lem6988635 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term371 A x f u v) = (term374 A x f u v).
Proof. exact (@lem6988634 A (@IN A) (term362 A x f u v)). Qed.
Lemma lem6988636 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem6988637 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term373 A x f v u) = (term375 A x f v u).
Proof. exact (MK_COMB (@lem6988635 A x f u v) (@lem6988636 A u)). Qed.
Lemma lem6988639 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988640 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6988639 (A -> Prop) Prop f x). Qed.
Lemma lem6988641 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term375 A x f v u) = (term376 A x f v u).
Proof. exact (@lem6988640 A (term374 A x f u v) u). Qed.
Lemma lem6988642 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term373 A x f v u) = (term376 A x f v u).
Proof. exact (TRANS (@lem6988637 A x f v u) (@lem6988641 A x f v u)). Qed.
Lemma lem6988643 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term372 A x f v u) = (term376 A x f v u).
Proof. exact (TRANS (@lem6988631 A x f v u) (@lem6988642 A x f v u)). Qed.
Lemma lem6988644 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term377 A x f v u) = (term378 A x f v u).
Proof. exact (MK_COMB (@lem6988601) (@lem6988643 A x f v u)). Qed.
Lemma lem6988645 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem6988654 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988655 {A : Type'} (f : type693 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6988654 (A -> nat) (type638 A) f x). Qed.
Lemma lem6988656 {A : Type'} (x : type693 A) (f : A -> nat) : (x f) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f).
Proof. exact (@lem6988655 A x f). Qed.
Lemma lem6988657 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem6988658 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (x f u) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f u).
Proof. exact (MK_COMB (@lem6988656 A x f) (@lem6988657 A u)). Qed.
Lemma lem6988660 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988661 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6988660 (A -> Prop) (type684 A) f x). Qed.
Lemma lem6988662 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f u) = (term360 A x f u).
Proof. exact (@lem6988661 A (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f) u). Qed.
Lemma lem6988663 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (x f u) = (term360 A x f u).
Proof. exact (TRANS (@lem6988658 A x f u) (@lem6988662 A x f u)). Qed.
Lemma lem6988664 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem6988665 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term361 A x f u v).
Proof. exact (MK_COMB (@lem6988663 A x f u) (@lem6988664 A v)). Qed.
Lemma lem6988667 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988668 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem6988667 (A -> Prop) A f x). Qed.
Lemma lem6988669 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term361 A x f u v) = (term362 A x f u v).
Proof. exact (@lem6988668 A (term360 A x f u) v). Qed.
Lemma lem6988671 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term362 A x f u v).
Proof. exact (TRANS (@lem6988665 A x f u v) (@lem6988669 A x f u v)). Qed.
Lemma lem6988672 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem6988673 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term370 A x f u v) = (term371 A x f u v).
Proof. exact (MK_COMB (@lem6988645 A) (@lem6988671 A x f u v)). Qed.
Lemma lem6988674 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term379 A x f u v) = (term380 A x f u v).
Proof. exact (MK_COMB (@lem6988673 A x f u v) (@lem6988672 A v)). Qed.
Lemma lem6988676 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988677 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6988676 A (type686 A) f x). Qed.
Lemma lem6988678 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term371 A x f u v) = (term374 A x f u v).
Proof. exact (@lem6988677 A (@IN A) (term362 A x f u v)). Qed.
Lemma lem6988679 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem6988680 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term380 A x f u v) = (term381 A x f u v).
Proof. exact (MK_COMB (@lem6988678 A x f u v) (@lem6988679 A v)). Qed.
Lemma lem6988682 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988683 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6988682 (A -> Prop) Prop f x). Qed.
Lemma lem6988684 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term381 A x f u v) = (term382 A x f u v).
Proof. exact (@lem6988683 A (term374 A x f u v) v). Qed.
Lemma lem6988685 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term380 A x f u v) = (term382 A x f u v).
Proof. exact (TRANS (@lem6988680 A x f u v) (@lem6988684 A x f u v)). Qed.
Lemma lem6988686 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term379 A x f u v) = (term382 A x f u v).
Proof. exact (TRANS (@lem6988674 A x f u v) (@lem6988685 A x f u v)). Qed.
Lemma lem6988687 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6988688 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term383 A x f u v) = (term384 A x f u v).
Proof. exact (MK_COMB (@lem6988687) (@lem6988686 A x f u v)). Qed.
Lemma lem6988689 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term385 A x f v u) = (term386 A x f v u).
Proof. exact (MK_COMB (@lem6988688 A x f u v) (@lem6988644 A x f v u)). Qed.
Lemma lem6988690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6988691 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term387 A x f v u) = (term388 A x f v u).
Proof. exact (MK_COMB (@lem6988690) (@lem6988689 A x f v u)). Qed.
Lemma lem6988692 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term389 A x f u v) = (term390 A x f u v).
Proof. exact (MK_COMB (@lem6988691 A x f v u) (@lem6988600 A x f u v)). Qed.
Lemma lem6988693 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6988700 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988701 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6988700 (A -> Prop) (type686 A) f x). Qed.
Lemma lem6988702 {A : Type'} (u : A -> Prop) : (@SUBSET A u) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) u).
Proof. exact (@lem6988701 A (@SUBSET A) u). Qed.
Lemma lem6988703 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem6988704 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@SUBSET A u v) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) u v).
Proof. exact (MK_COMB (@lem6988702 A u) (@lem6988703 A v)). Qed.
Lemma lem6988706 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988707 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6988706 (A -> Prop) Prop f x). Qed.
Lemma lem6988708 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) u v) = (term391 A u v).
Proof. exact (@lem6988707 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) u) v). Qed.
Lemma lem6988710 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@SUBSET A u v) = (term391 A u v).
Proof. exact (TRANS (@lem6988704 A u v) (@lem6988708 A u v)). Qed.
Lemma lem6988711 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term256 A u v) = (term392 A u v).
Proof. exact (MK_COMB (@lem6988693) (@lem6988710 A u v)). Qed.
Lemma lem6988712 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6988713 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term238 A u v) = (term393 A u v).
Proof. exact (MK_COMB (@lem6988712) (@lem6988711 A u v)). Qed.
Lemma lem6988714 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term394 A x f u v) = (term395 A x f u v).
Proof. exact (MK_COMB (@lem6988713 A u v) (@lem6988692 A x f u v)). Qed.
Lemma lem6988715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6988716 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term396 A x f u v) = (term397 A x f u v).
Proof. exact (MK_COMB (@lem6988715) (@lem6988714 A x f u v)). Qed.
Lemma lem6988717 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term398 A x v u f) = (term399 A x v u f).
Proof. exact (MK_COMB (@lem6988716 A x f u v) (@lem6988554 A v u f)). Qed.
Lemma lem6988718 {A : Type'} (x : type693 A) (u : A -> Prop) (f : A -> nat) : (term400 A x u f) = (term401 A x u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6988717 A x v u f)). Qed.
Lemma lem6988719 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6988720 {A : Type'} (x : type693 A) (u : A -> Prop) (f : A -> nat) : (term402 A x u f) = (term403 A x u f).
Proof. exact (MK_COMB (@lem6988719 A) (@lem6988718 A x u f)). Qed.
Lemma lem6988721 {A : Type'} (x : type693 A) (f : A -> nat) : (term404 A x f) = (term405 A x f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6988720 A x u f)). Qed.
Lemma lem6988722 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6988723 {A : Type'} (x : type693 A) (f : A -> nat) : (term349 A x f) = (term406 A x f).
Proof. exact (MK_COMB (@lem6988722 A) (@lem6988721 A x f)). Qed.
Lemma lem6988724 {A : Type'} (x : type693 A) : (term351 A x) = (term407 A x).
Proof. exact (fun_ext (fun f : A -> nat => @lem6988723 A x f)). Qed.
Lemma lem6988725 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6988726 {A : Type'} (x : type693 A) : (term353 A x) = (term408 A x).
Proof. exact (MK_COMB (@lem6988725 A) (@lem6988724 A x)). Qed.
Lemma lem6988727 {A : Type'} (x : type693 A) (h1 : term353 A x) : term408 A x.
Proof. exact (EQ_MP (@lem6988726 A x) (@lem6988512 A x h1)). Qed.
Lemma lem6988728 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6988735 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988736 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem6988735 (A -> Prop) (type705 A) f x). Qed.
Lemma lem6988737 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s).
Proof. exact (@lem6988736 A (@nsum A) s). Qed.
Lemma lem6988738 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6988739 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s f).
Proof. exact (MK_COMB (@lem6988737 A s) (@lem6988738 A f)). Qed.
Lemma lem6988741 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988742 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem6988741 (A -> nat) nat f x). Qed.
Lemma lem6988743 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s f) = (term357 A s f).
Proof. exact (@lem6988742 A (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s) f). Qed.
Lemma lem6988745 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (term357 A s f).
Proof. exact (TRANS (@lem6988739 A s f) (@lem6988743 A s f)). Qed.
Lemma lem6988752 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988753 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem6988752 (A -> Prop) (type705 A) f x). Qed.
Lemma lem6988754 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s).
Proof. exact (@lem6988753 A (@nsum A) s). Qed.
Lemma lem6988755 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6988756 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@nsum A s g) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s g).
Proof. exact (MK_COMB (@lem6988754 A s) (@lem6988755 A g)). Qed.
Lemma lem6988758 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988759 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem6988758 (A -> nat) nat f x). Qed.
Lemma lem6988760 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s g) = (term357 A s g).
Proof. exact (@lem6988759 A (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s) g). Qed.
Lemma lem6988762 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@nsum A s g) = (term357 A s g).
Proof. exact (TRANS (@lem6988756 A s g) (@lem6988760 A s g)). Qed.
Lemma lem6988763 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term358 A s f) = (term359 A s f).
Proof. exact (MK_COMB (@lem6988728) (@lem6988745 A s f)). Qed.
Lemma lem6988764 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : ((@nsum A s f) = (@nsum A s g)) = ((term357 A s f) = (term357 A s g)).
Proof. exact (MK_COMB (@lem6988763 A s f) (@lem6988762 A s g)). Qed.
Lemma lem6988765 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6988766 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6988767 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6988776 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988777 {A : Type'} (f : type695 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6988776 (A -> nat) (type694 A) f x). Qed.
Lemma lem6988778 {A : Type'} (x' : type695 A) (f : A -> nat) : (x' f) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x' f).
Proof. exact (@lem6988777 A x' f). Qed.
Lemma lem6988779 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6988780 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) : (x' f g) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x' f g).
Proof. exact (MK_COMB (@lem6988778 A x' f) (@lem6988779 A g)). Qed.
Lemma lem6988782 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988783 {A : Type'} (f : type694 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6988782 (A -> nat) (type684 A) f x). Qed.
Lemma lem6988784 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) : (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x' f g) = (term409 A x' f g).
Proof. exact (@lem6988783 A (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x' f) g). Qed.
Lemma lem6988785 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) : (x' f g) = (term409 A x' f g).
Proof. exact (TRANS (@lem6988780 A x' f g) (@lem6988784 A x' f g)). Qed.
Lemma lem6988786 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6988787 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x' f g s) = (term410 A x' f g s).
Proof. exact (MK_COMB (@lem6988785 A x' f g) (@lem6988786 A s)). Qed.
Lemma lem6988789 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988790 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem6988789 (A -> Prop) A f x). Qed.
Lemma lem6988791 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term410 A x' f g s) = (term411 A x' f g s).
Proof. exact (@lem6988790 A (term409 A x' f g) s). Qed.
Lemma lem6988793 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x' f g s) = (term411 A x' f g s).
Proof. exact (TRANS (@lem6988787 A x' f g s) (@lem6988791 A x' f g s)). Qed.
Lemma lem6988794 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term412 A x' f g s) = (term413 A x' f g s).
Proof. exact (MK_COMB (@lem6988767 A f) (@lem6988793 A x' f g s)). Qed.
Lemma lem6988796 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988797 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem6988796 A nat f x). Qed.
Lemma lem6988798 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term413 A x' f g s) = (term414 A x' f g s).
Proof. exact (@lem6988797 A f (term411 A x' f g s)). Qed.
Lemma lem6988799 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term412 A x' f g s) = (term414 A x' f g s).
Proof. exact (TRANS (@lem6988794 A x' f g s) (@lem6988798 A x' f g s)). Qed.
Lemma lem6988800 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6988809 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988810 {A : Type'} (f : type695 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6988809 (A -> nat) (type694 A) f x). Qed.
Lemma lem6988811 {A : Type'} (x' : type695 A) (f : A -> nat) : (x' f) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x' f).
Proof. exact (@lem6988810 A x' f). Qed.
Lemma lem6988812 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6988813 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) : (x' f g) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x' f g).
Proof. exact (MK_COMB (@lem6988811 A x' f) (@lem6988812 A g)). Qed.
Lemma lem6988815 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988816 {A : Type'} (f : type694 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6988815 (A -> nat) (type684 A) f x). Qed.
Lemma lem6988817 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) : (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x' f g) = (term409 A x' f g).
Proof. exact (@lem6988816 A (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x' f) g). Qed.
Lemma lem6988818 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) : (x' f g) = (term409 A x' f g).
Proof. exact (TRANS (@lem6988813 A x' f g) (@lem6988817 A x' f g)). Qed.
Lemma lem6988819 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6988820 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x' f g s) = (term410 A x' f g s).
Proof. exact (MK_COMB (@lem6988818 A x' f g) (@lem6988819 A s)). Qed.
Lemma lem6988822 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988823 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem6988822 (A -> Prop) A f x). Qed.
Lemma lem6988824 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term410 A x' f g s) = (term411 A x' f g s).
Proof. exact (@lem6988823 A (term409 A x' f g) s). Qed.
Lemma lem6988826 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x' f g s) = (term411 A x' f g s).
Proof. exact (TRANS (@lem6988820 A x' f g s) (@lem6988824 A x' f g s)). Qed.
Lemma lem6988827 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term415 A x' f g s) = (term416 A x' f g s).
Proof. exact (MK_COMB (@lem6988800 A g) (@lem6988826 A x' f g s)). Qed.
Lemma lem6988829 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988830 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem6988829 A nat f x). Qed.
Lemma lem6988831 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term416 A x' f g s) = (term417 A x' f g s).
Proof. exact (@lem6988830 A g (term411 A x' f g s)). Qed.
Lemma lem6988832 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term415 A x' f g s) = (term417 A x' f g s).
Proof. exact (TRANS (@lem6988827 A x' f g s) (@lem6988831 A x' f g s)). Qed.
Lemma lem6988833 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term418 A x' f g s) = (term419 A x' f g s).
Proof. exact (MK_COMB (@lem6988766) (@lem6988799 A x' f g s)). Qed.
Lemma lem6988834 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : ((term412 A x' f g s) = (term415 A x' f g s)) = ((term414 A x' f g s) = (term417 A x' f g s)).
Proof. exact (MK_COMB (@lem6988833 A x' f g s) (@lem6988832 A x' f g s)). Qed.
Lemma lem6988835 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term420 A x' f g s) = (term421 A x' f g s).
Proof. exact (MK_COMB (@lem6988765) (@lem6988834 A x' f g s)). Qed.
Lemma lem6988836 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem6988845 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988846 {A : Type'} (f : type695 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6988845 (A -> nat) (type694 A) f x). Qed.
Lemma lem6988847 {A : Type'} (x' : type695 A) (f : A -> nat) : (x' f) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x' f).
Proof. exact (@lem6988846 A x' f). Qed.
Lemma lem6988848 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6988849 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) : (x' f g) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x' f g).
Proof. exact (MK_COMB (@lem6988847 A x' f) (@lem6988848 A g)). Qed.
Lemma lem6988851 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988852 {A : Type'} (f : type694 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6988851 (A -> nat) (type684 A) f x). Qed.
Lemma lem6988853 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) : (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x' f g) = (term409 A x' f g).
Proof. exact (@lem6988852 A (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x' f) g). Qed.
Lemma lem6988854 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) : (x' f g) = (term409 A x' f g).
Proof. exact (TRANS (@lem6988849 A x' f g) (@lem6988853 A x' f g)). Qed.
Lemma lem6988855 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6988856 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x' f g s) = (term410 A x' f g s).
Proof. exact (MK_COMB (@lem6988854 A x' f g) (@lem6988855 A s)). Qed.
Lemma lem6988858 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988859 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem6988858 (A -> Prop) A f x). Qed.
Lemma lem6988860 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term410 A x' f g s) = (term411 A x' f g s).
Proof. exact (@lem6988859 A (term409 A x' f g) s). Qed.
Lemma lem6988862 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x' f g s) = (term411 A x' f g s).
Proof. exact (TRANS (@lem6988856 A x' f g s) (@lem6988860 A x' f g s)). Qed.
Lemma lem6988863 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6988864 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term422 A x' f g s) = (term423 A x' f g s).
Proof. exact (MK_COMB (@lem6988836 A) (@lem6988862 A x' f g s)). Qed.
Lemma lem6988865 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term424 A x' f g s) = (term425 A x' f g s).
Proof. exact (MK_COMB (@lem6988864 A x' f g s) (@lem6988863 A s)). Qed.
Lemma lem6988867 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988868 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6988867 A (type686 A) f x). Qed.
Lemma lem6988869 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term423 A x' f g s) = (term426 A x' f g s).
Proof. exact (@lem6988868 A (@IN A) (term411 A x' f g s)). Qed.
Lemma lem6988870 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6988871 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term425 A x' f g s) = (term427 A x' f g s).
Proof. exact (MK_COMB (@lem6988869 A x' f g s) (@lem6988870 A s)). Qed.
Lemma lem6988873 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6988874 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6988873 (A -> Prop) Prop f x). Qed.
Lemma lem6988875 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term427 A x' f g s) = (term428 A x' f g s).
Proof. exact (@lem6988874 A (term426 A x' f g s) s). Qed.
Lemma lem6988876 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term425 A x' f g s) = (term428 A x' f g s).
Proof. exact (TRANS (@lem6988871 A x' f g s) (@lem6988875 A x' f g s)). Qed.
Lemma lem6988877 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term424 A x' f g s) = (term428 A x' f g s).
Proof. exact (TRANS (@lem6988865 A x' f g s) (@lem6988876 A x' f g s)). Qed.
Lemma lem6988878 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6988879 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term429 A x' f g s) = (term430 A x' f g s).
Proof. exact (MK_COMB (@lem6988878) (@lem6988877 A x' f g s)). Qed.
Lemma lem6988880 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term431 A x' f g s) = (term432 A x' f g s).
Proof. exact (MK_COMB (@lem6988879 A x' f g s) (@lem6988835 A x' f g s)). Qed.
Lemma lem6988881 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6988882 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term433 A x' f g s) = (term434 A x' f g s).
Proof. exact (MK_COMB (@lem6988881) (@lem6988880 A x' f g s)). Qed.
Lemma lem6988883 {A : Type'} (x' : type695 A) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term435 A x' f s g) = (term436 A x' f s g).
Proof. exact (MK_COMB (@lem6988882 A x' f g s) (@lem6988764 A f s g)). Qed.
Lemma lem6988884 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) : (term437 A x' f g) = (term438 A x' f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6988883 A x' f s g)). Qed.
Lemma lem6988885 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6988886 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) : (term439 A x' f g) = (term440 A x' f g).
Proof. exact (MK_COMB (@lem6988885 A) (@lem6988884 A x' f g)). Qed.
Lemma lem6988887 {A : Type'} (x' : type695 A) (f : A -> nat) : (term441 A x' f) = (term442 A x' f).
Proof. exact (fun_ext (fun g : A -> nat => @lem6988886 A x' f g)). Qed.
Lemma lem6988888 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6988889 {A : Type'} (x' : type695 A) (f : A -> nat) : (term221 A x' f) = (term443 A x' f).
Proof. exact (MK_COMB (@lem6988888 A) (@lem6988887 A x' f)). Qed.
Lemma lem6988890 {A : Type'} (x' : type695 A) : (term223 A x') = (term444 A x').
Proof. exact (fun_ext (fun f : A -> nat => @lem6988889 A x' f)). Qed.
Lemma lem6988891 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6988892 {A : Type'} (x' : type695 A) : (term225 A x') = (term445 A x').
Proof. exact (MK_COMB (@lem6988891 A) (@lem6988890 A x')). Qed.
Lemma lem6988893 {A : Type'} (x' : type695 A) (h1 : term225 A x') : term445 A x'.
Proof. exact (EQ_MP (@lem6988892 A x') (@lem6988513 A x' h1)). Qed.
Lemma lem6989060 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6989061 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6989068 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6989069 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem6989068 (A -> Prop) (type705 A) f x). Qed.
Lemma lem6989070 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s).
Proof. exact (@lem6989069 A (@nsum A) s). Qed.
Lemma lem6989071 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6989072 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s f).
Proof. exact (MK_COMB (@lem6989070 A s) (@lem6989071 A f)). Qed.
Lemma lem6989074 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6989075 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem6989074 (A -> nat) nat f x). Qed.
Lemma lem6989076 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s f) = (term357 A s f).
Proof. exact (@lem6989075 A (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s) f). Qed.
Lemma lem6989078 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (term357 A s f).
Proof. exact (TRANS (@lem6989072 A s f) (@lem6989076 A s f)). Qed.
Lemma lem6989085 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6989086 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem6989085 (A -> Prop) (type705 A) f x). Qed.
Lemma lem6989087 {A : Type'} (t : A -> Prop) : (@nsum A t) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) t).
Proof. exact (@lem6989086 A (@nsum A) t). Qed.
Lemma lem6989088 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6989089 {A : Type'} (t : A -> Prop) (g : A -> nat) : (@nsum A t g) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) t g).
Proof. exact (MK_COMB (@lem6989087 A t) (@lem6989088 A g)). Qed.
Lemma lem6989091 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6989092 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem6989091 (A -> nat) nat f x). Qed.
Lemma lem6989093 {A : Type'} (t : A -> Prop) (g : A -> nat) : (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) t g) = (term357 A t g).
Proof. exact (@lem6989092 A (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) t) g). Qed.
Lemma lem6989095 {A : Type'} (t : A -> Prop) (g : A -> nat) : (@nsum A t g) = (term357 A t g).
Proof. exact (TRANS (@lem6989089 A t g) (@lem6989093 A t g)). Qed.
Lemma lem6989096 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term358 A s f) = (term359 A s f).
Proof. exact (MK_COMB (@lem6989061) (@lem6989078 A s f)). Qed.
Lemma lem6989097 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) : ((@nsum A s f) = (@nsum A t g)) = ((term357 A s f) = (term357 A t g)).
Proof. exact (MK_COMB (@lem6989096 A s f) (@lem6989095 A t g)). Qed.
Lemma lem6989098 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) : (term84 A s f t g) = (term446 A s f t g).
Proof. exact (MK_COMB (@lem6989060) (@lem6989097 A s f t g)). Qed.
Lemma lem6989099 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6989104 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6989106 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem6989104 A nat f x). Qed.
Lemma lem6989111 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6989112 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem6989111 nat nat f x). Qed.
Lemma lem6989114 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem6989112 NUMERAL 0). Qed.
Lemma lem6989115 {A : Type'} (f : A -> nat) (x : A) : (term447 A f x) = (term448 A f x).
Proof. exact (MK_COMB (@lem6989099) (@lem6989106 A f x)). Qed.
Lemma lem6989116 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((@I (A -> nat) f x) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (MK_COMB (@lem6989115 A f x) (@lem6989114)). Qed.
Lemma lem6989123 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6989124 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6989123 A (type686 A) f x). Qed.
Lemma lem6989125 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem6989124 A (@IN A) x). Qed.
Lemma lem6989126 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6989127 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x t).
Proof. exact (MK_COMB (@lem6989125 A x) (@lem6989126 A t)). Qed.
Lemma lem6989129 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6989130 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6989129 (A -> Prop) Prop f x). Qed.
Lemma lem6989131 {A : Type'} (x : A) (t : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x t) = (term449 A x t).
Proof. exact (@lem6989130 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) t). Qed.
Lemma lem6989133 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (term449 A x t).
Proof. exact (TRANS (@lem6989127 A x t) (@lem6989131 A x t)). Qed.
Lemma lem6989134 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6989141 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6989142 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6989141 A (type686 A) f x). Qed.
Lemma lem6989143 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem6989142 A (@IN A) x). Qed.
Lemma lem6989144 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6989145 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem6989143 A x) (@lem6989144 A s)). Qed.
Lemma lem6989147 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6989148 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6989147 (A -> Prop) Prop f x). Qed.
Lemma lem6989149 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term449 A x s).
Proof. exact (@lem6989148 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem6989151 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term449 A x s).
Proof. exact (TRANS (@lem6989145 A x s) (@lem6989149 A x s)). Qed.
Lemma lem6989152 {A : Type'} (x : A) (s : A -> Prop) : (term72 A x s) = (term450 A x s).
Proof. exact (MK_COMB (@lem6989134) (@lem6989151 A x s)). Qed.
Lemma lem6989153 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6989154 {A : Type'} (x : A) (s : A -> Prop) : (term68 A x s) = (term451 A x s).
Proof. exact (MK_COMB (@lem6989153) (@lem6989152 A x s)). Qed.
Lemma lem6989155 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term70 A s x t) = (term452 A s x t).
Proof. exact (MK_COMB (@lem6989154 A x s) (@lem6989133 A x t)). Qed.
Lemma lem6989156 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6989157 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term74 A s x t) = (term453 A s x t).
Proof. exact (MK_COMB (@lem6989156) (@lem6989155 A s x t)). Qed.
Lemma lem6989158 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) (x : A) : (term76 A s t f x) = (term454 A s t f x).
Proof. exact (MK_COMB (@lem6989157 A s x t) (@lem6989116 A f x)). Qed.
Lemma lem6989159 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term78 A s t f) = (term455 A s t f).
Proof. exact (fun_ext (fun x : A => @lem6989158 A s t f x)). Qed.
Lemma lem6989160 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6989161 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term79 A s t f) = (term456 A s t f).
Proof. exact (MK_COMB (@lem6989160 A) (@lem6989159 A s t f)). Qed.
Lemma lem6989162 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6989167 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6989169 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem6989167 A nat f x). Qed.
Lemma lem6989174 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6989175 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem6989174 A nat f x). Qed.
Lemma lem6989177 {A : Type'} (g : A -> nat) (x : A) : (g x) = (@I (A -> nat) g x).
Proof. exact (@lem6989175 A g x). Qed.
Lemma lem6989178 {A : Type'} (f : A -> nat) (x : A) : (term447 A f x) = (term448 A f x).
Proof. exact (MK_COMB (@lem6989162) (@lem6989169 A f x)). Qed.
Lemma lem6989179 {A : Type'} (f : A -> nat) (g : A -> nat) (x : A) : ((f x) = (g x)) = ((@I (A -> nat) f x) = (@I (A -> nat) g x)).
Proof. exact (MK_COMB (@lem6989178 A f x) (@lem6989177 A g x)). Qed.
Lemma lem6989180 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6989187 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6989188 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6989187 A (type686 A) f x). Qed.
Lemma lem6989189 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem6989188 A (@IN A) x). Qed.
Lemma lem6989190 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6989191 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x t).
Proof. exact (MK_COMB (@lem6989189 A x) (@lem6989190 A t)). Qed.
Lemma lem6989193 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6989194 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6989193 (A -> Prop) Prop f x). Qed.
Lemma lem6989195 {A : Type'} (x : A) (t : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x t) = (term449 A x t).
Proof. exact (@lem6989194 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) t). Qed.
Lemma lem6989197 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (term449 A x t).
Proof. exact (TRANS (@lem6989191 A x t) (@lem6989195 A x t)). Qed.
Lemma lem6989198 {A : Type'} (x : A) (t : A -> Prop) : (term72 A x t) = (term450 A x t).
Proof. exact (MK_COMB (@lem6989180) (@lem6989197 A x t)). Qed.
Lemma lem6989199 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6989200 {A : Type'} (x : A) (t : A -> Prop) : (term68 A x t) = (term451 A x t).
Proof. exact (MK_COMB (@lem6989199) (@lem6989198 A x t)). Qed.
Lemma lem6989201 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term64 A t f g x) = (term457 A t f g x).
Proof. exact (MK_COMB (@lem6989200 A x t) (@lem6989179 A f g x)). Qed.
Lemma lem6989202 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) : (term65 A t f g) = (term458 A t f g).
Proof. exact (fun_ext (fun x : A => @lem6989201 A t f g x)). Qed.
Lemma lem6989203 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6989204 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) : (term66 A t f g) = (term459 A t f g).
Proof. exact (MK_COMB (@lem6989203 A) (@lem6989202 A t f g)). Qed.
Lemma lem6989205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6989206 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) : (term80 A t f g) = (term460 A t f g).
Proof. exact (MK_COMB (@lem6989205) (@lem6989204 A t f g)). Qed.
Lemma lem6989207 {A : Type'} (g : A -> nat) (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term81 A g s t f) = (term461 A g s t f).
Proof. exact (MK_COMB (@lem6989206 A t f g) (@lem6989161 A s t f)). Qed.
Lemma lem6989214 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6989215 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6989214 (A -> Prop) (type686 A) f x). Qed.
Lemma lem6989216 {A : Type'} (t : A -> Prop) : (@SUBSET A t) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) t).
Proof. exact (@lem6989215 A (@SUBSET A) t). Qed.
Lemma lem6989217 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6989218 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) t s).
Proof. exact (MK_COMB (@lem6989216 A t) (@lem6989217 A s)). Qed.
Lemma lem6989220 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6989221 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6989220 (A -> Prop) Prop f x). Qed.
Lemma lem6989222 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) t s) = (term391 A t s).
Proof. exact (@lem6989221 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) t) s). Qed.
Lemma lem6989224 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term391 A t s).
Proof. exact (TRANS (@lem6989218 A t s) (@lem6989222 A t s)). Qed.
Lemma lem6989225 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6989226 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term33 A t s) = (term462 A t s).
Proof. exact (MK_COMB (@lem6989225) (@lem6989224 A t s)). Qed.
Lemma lem6989227 {A : Type'} (g : A -> nat) (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term82 A g s t f) = (term463 A g s t f).
Proof. exact (MK_COMB (@lem6989226 A t s) (@lem6989207 A g s t f)). Qed.
Lemma lem6989232 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6989233 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6989232 (A -> Prop) Prop f x). Qed.
Lemma lem6989235 {A : Type'} (t : A -> Prop) : (@FINITE A t) = (@I ((A -> Prop) -> Prop) (@FINITE A) t).
Proof. exact (@lem6989233 A (@FINITE A) t). Qed.
Lemma lem6989236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6989237 {A : Type'} (t : A -> Prop) : (term55 A t) = (term464 A t).
Proof. exact (MK_COMB (@lem6989236) (@lem6989235 A t)). Qed.
Lemma lem6989238 {A : Type'} (g : A -> nat) (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term83 A g s t f) = (term465 A g s t f).
Proof. exact (MK_COMB (@lem6989237 A t) (@lem6989227 A g s t f)). Qed.
Lemma lem6989239 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6989240 {A : Type'} (g : A -> nat) (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term86 A g s t f) = (term466 A g s t f).
Proof. exact (MK_COMB (@lem6989239) (@lem6989238 A g s t f)). Qed.
Lemma lem6989241 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) : (term88 A s f t g) = (term467 A s f t g).
Proof. exact (MK_COMB (@lem6989240 A g s t f) (@lem6989098 A s f t g)). Qed.
Lemma lem6989242 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term467 A s f t g.
Proof. exact (EQ_MP (@lem6989241 A s f t g) (@lem6988517 A s f t g h1)). Qed.
Lemma lem6989244 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term465 A g s t f.
Proof. exact (proj1 (@lem6989242 A s f t g h1)). Qed.
Lemma lem6989245 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term463 A g s t f.
Proof. exact (proj2 (@lem6989244 A s f t g h1)). Qed.
Lemma lem6989247 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term461 A g s t f.
Proof. exact (proj2 (@lem6989245 A s f t g h1)). Qed.
Lemma lem6989249 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term456 A s t f.
Proof. exact (proj2 (@lem6989247 A s f t g h1)). Qed.
Lemma lem6989250 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term459 A t f g.
Proof. exact (proj1 (@lem6989247 A s f t g h1)). Qed.
Lemma lem6989252 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term357 A v f) = (term357 A u f)) = ((term357 A v f) = (term357 A u f)).
Proof. exact (eq_refl ((term357 A v f) = (term357 A u f))). Qed.
Lemma lem6989266 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term395 A x f u v) = (term468 A x f u v).
Proof. exact (@lem19490 (term386 A x f v u) (term392 A u v) (term369 A x f u v)). Qed.
Lemma lem6989267 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term469 A x f u v) = (term469 A x f u v).
Proof. exact (eq_refl (term469 A x f u v)). Qed.
Lemma lem6989274 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term470 A x f v u) = (term471 A x f v u).
Proof. exact (@lem19490 (term382 A x f u v) (term392 A u v) (term378 A x f v u)). Qed.
Lemma lem6989275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6989276 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term472 A x f v u) = (term473 A x f v u).
Proof. exact (MK_COMB (@lem6989275) (@lem6989274 A x f v u)). Qed.
Lemma lem6989277 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term468 A x f u v) = (term474 A x f u v).
Proof. exact (MK_COMB (@lem6989276 A x f v u) (@lem6989267 A x f u v)). Qed.
Lemma lem6989279 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term395 A x f u v) = (term474 A x f u v).
Proof. exact (TRANS (@lem6989266 A x f u v) (@lem6989277 A x f u v)). Qed.
Lemma lem6989280 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6989281 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term397 A x f u v) = (term475 A x f u v).
Proof. exact (MK_COMB (@lem6989280) (@lem6989279 A x f u v)). Qed.
Lemma lem6989282 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term399 A x v u f) = (term476 A x v u f).
Proof. exact (MK_COMB (@lem6989281 A x f u v) (@lem6989252 A v u f)). Qed.
Lemma lem6989283 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term476 A x v u f) = (term477 A x v u f).
Proof. exact (@lem19699 (term471 A x f v u) (term469 A x f u v) ((term357 A v f) = (term357 A u f))). Qed.
Lemma lem6989284 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term478 A x v u f) = (term478 A x v u f).
Proof. exact (eq_refl (term478 A x v u f)). Qed.
Lemma lem6989291 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term479 A x v u f) = (term480 A x v u f).
Proof. exact (@lem19699 (term481 A x f u v) (term482 A x f v u) ((term357 A v f) = (term357 A u f))). Qed.
Lemma lem6989292 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6989293 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term483 A x v u f) = (term484 A x v u f).
Proof. exact (MK_COMB (@lem6989292) (@lem6989291 A x v u f)). Qed.
Lemma lem6989294 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term477 A x v u f) = (term485 A x v u f).
Proof. exact (MK_COMB (@lem6989293 A x v u f) (@lem6989284 A x v u f)). Qed.
Lemma lem6989295 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term476 A x v u f) = (term485 A x v u f).
Proof. exact (TRANS (@lem6989283 A x v u f) (@lem6989294 A x v u f)). Qed.
Lemma lem6989296 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term399 A x v u f) = (term485 A x v u f).
Proof. exact (TRANS (@lem6989282 A x v u f) (@lem6989295 A x v u f)). Qed.
Lemma lem6989297 {A : Type'} (x : type693 A) (u : A -> Prop) (f : A -> nat) : (term401 A x u f) = (term486 A x u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6989296 A x v u f)). Qed.
Lemma lem6989298 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6989299 {A : Type'} (x : type693 A) (u : A -> Prop) (f : A -> nat) : (term403 A x u f) = (term487 A x u f).
Proof. exact (MK_COMB (@lem6989298 A) (@lem6989297 A x u f)). Qed.
Lemma lem6989300 {A : Type'} (x : type693 A) (f : A -> nat) : (term405 A x f) = (term488 A x f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6989299 A x u f)). Qed.
Lemma lem6989301 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6989302 {A : Type'} (x : type693 A) (f : A -> nat) : (term406 A x f) = (term489 A x f).
Proof. exact (MK_COMB (@lem6989301 A) (@lem6989300 A x f)). Qed.
Lemma lem6989303 {A : Type'} (x : type693 A) : (term407 A x) = (term490 A x).
Proof. exact (fun_ext (fun f : A -> nat => @lem6989302 A x f)). Qed.
Lemma lem6989304 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6989306 {A : Type'} (x : type693 A) : (term408 A x) = (term491 A x).
Proof. exact (MK_COMB (@lem6989304 A) (@lem6989303 A x)). Qed.
Lemma lem6989307 {A : Type'} (x : type693 A) (h1 : term353 A x) : term491 A x.
Proof. exact (EQ_MP (@lem6989306 A x) (@lem6988727 A x h1)). Qed.
Lemma lem6989325 {A : Type'} (x' : type695 A) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term436 A x' f s g) = (term492 A x' f s g).
Proof. exact (@lem19699 (term428 A x' f g s) (term421 A x' f g s) ((term357 A s f) = (term357 A s g))). Qed.
Lemma lem6989326 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) : (term438 A x' f g) = (term493 A x' f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6989325 A x' f s g)). Qed.
Lemma lem6989327 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6989328 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) : (term440 A x' f g) = (term494 A x' f g).
Proof. exact (MK_COMB (@lem6989327 A) (@lem6989326 A x' f g)). Qed.
Lemma lem6989329 {A : Type'} (x' : type695 A) (f : A -> nat) : (term442 A x' f) = (term495 A x' f).
Proof. exact (fun_ext (fun g : A -> nat => @lem6989328 A x' f g)). Qed.
Lemma lem6989330 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6989331 {A : Type'} (x' : type695 A) (f : A -> nat) : (term443 A x' f) = (term496 A x' f).
Proof. exact (MK_COMB (@lem6989330 A) (@lem6989329 A x' f)). Qed.
Lemma lem6989332 {A : Type'} (x' : type695 A) : (term444 A x') = (term497 A x').
Proof. exact (fun_ext (fun f : A -> nat => @lem6989331 A x' f)). Qed.
Lemma lem6989333 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6989335 {A : Type'} (x' : type695 A) : (term445 A x') = (term498 A x').
Proof. exact (MK_COMB (@lem6989333 A) (@lem6989332 A x')). Qed.
Lemma lem6989336 {A : Type'} (x' : type695 A) (h1 : term225 A x') : term498 A x'.
Proof. exact (EQ_MP (@lem6989335 A x') (@lem6988893 A x' h1)). Qed.
Lemma lem6989385 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term457 A t f g x) = (term457 A t f g x).
Proof. exact (eq_refl (term457 A t f g x)). Qed.
Lemma lem6989386 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) : (term458 A t f g) = (term458 A t f g).
Proof. exact (fun_ext (fun x : A => @lem6989385 A t f g x)). Qed.
Lemma lem6989387 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6989389 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) : (term459 A t f g) = (term459 A t f g).
Proof. exact (MK_COMB (@lem6989387 A) (@lem6989386 A t f g)). Qed.
Lemma lem6989390 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term459 A t f g.
Proof. exact (EQ_MP (@lem6989389 A t f g) (@lem6989250 A s f t g h1)). Qed.
Lemma lem6989404 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) (x : A) : (term454 A s t f x) = (term454 A s t f x).
Proof. exact (eq_refl (term454 A s t f x)). Qed.
Lemma lem6989405 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term455 A s t f) = (term455 A s t f).
Proof. exact (fun_ext (fun x : A => @lem6989404 A s t f x)). Qed.
Lemma lem6989406 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6989408 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term456 A s t f) = (term456 A s t f).
Proof. exact (MK_COMB (@lem6989406 A) (@lem6989405 A s t f)). Qed.
Lemma lem6989409 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term456 A s t f.
Proof. exact (EQ_MP (@lem6989408 A s t f) (@lem6989249 A s f t g h1)). Qed.
Lemma lem6989410 {A : Type'} (_93128 : A -> nat) (x : type693 A) (h1 : term353 A x) : term499 A x _93128.
Proof. exact (@lem6989307 A x h1 _93128). Qed.
Lemma lem6989411 {A : Type'} (x : type693 A) (_93128 : A -> nat) : (term499 A x _93128) = (term489 A x _93128).
Proof. exact (eq_refl (term499 A x _93128)). Qed.
Lemma lem6989412 {A : Type'} (_93128 : A -> nat) (x : type693 A) (h1 : term353 A x) : term489 A x _93128.
Proof. exact (EQ_MP (@lem6989411 A x _93128) (@lem6989410 A _93128 x h1)). Qed.
Lemma lem6989413 {A : Type'} (_93128 : A -> nat) (_93129 : A -> Prop) (x : type693 A) (h1 : term353 A x) : term500 A x _93128 _93129.
Proof. exact (@lem6989412 A _93128 x h1 _93129). Qed.
Lemma lem6989414 {A : Type'} (x : type693 A) (_93129 : A -> Prop) (_93128 : A -> nat) : (term500 A x _93128 _93129) = (term487 A x _93129 _93128).
Proof. exact (eq_refl (term500 A x _93128 _93129)). Qed.
Lemma lem6989415 {A : Type'} (_93129 : A -> Prop) (_93128 : A -> nat) (x : type693 A) (h1 : term353 A x) : term487 A x _93129 _93128.
Proof. exact (EQ_MP (@lem6989414 A x _93129 _93128) (@lem6989413 A _93128 _93129 x h1)). Qed.
Lemma lem6989416 {A : Type'} (_93129 : A -> Prop) (_93128 : A -> nat) (_93130 : A -> Prop) (x : type693 A) (h1 : term353 A x) : term501 A x _93129 _93128 _93130.
Proof. exact (@lem6989415 A _93129 _93128 x h1 _93130). Qed.
Lemma lem6989417 {A : Type'} (x : type693 A) (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term501 A x _93129 _93128 _93130) = (term485 A x _93130 _93129 _93128).
Proof. exact (eq_refl (term501 A x _93129 _93128 _93130)). Qed.
Lemma lem6989418 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) (x : type693 A) (h1 : term353 A x) : term485 A x _93130 _93129 _93128.
Proof. exact (EQ_MP (@lem6989417 A x _93130 _93129 _93128) (@lem6989416 A _93129 _93128 _93130 x h1)). Qed.
Lemma lem6989419 {A : Type'} (_93131 : A -> nat) (x' : type695 A) (h1 : term225 A x') : term502 A x' _93131.
Proof. exact (@lem6989336 A x' h1 _93131). Qed.
Lemma lem6989420 {A : Type'} (x' : type695 A) (_93131 : A -> nat) : (term502 A x' _93131) = (term496 A x' _93131).
Proof. exact (eq_refl (term502 A x' _93131)). Qed.
Lemma lem6989421 {A : Type'} (_93131 : A -> nat) (x' : type695 A) (h1 : term225 A x') : term496 A x' _93131.
Proof. exact (EQ_MP (@lem6989420 A x' _93131) (@lem6989419 A _93131 x' h1)). Qed.
Lemma lem6989422 {A : Type'} (_93131 : A -> nat) (_93132 : A -> nat) (x' : type695 A) (h1 : term225 A x') : term503 A x' _93131 _93132.
Proof. exact (@lem6989421 A _93131 x' h1 _93132). Qed.
Lemma lem6989423 {A : Type'} (x' : type695 A) (_93131 : A -> nat) (_93132 : A -> nat) : (term503 A x' _93131 _93132) = (term494 A x' _93131 _93132).
Proof. exact (eq_refl (term503 A x' _93131 _93132)). Qed.
Lemma lem6989424 {A : Type'} (_93131 : A -> nat) (_93132 : A -> nat) (x' : type695 A) (h1 : term225 A x') : term494 A x' _93131 _93132.
Proof. exact (EQ_MP (@lem6989423 A x' _93131 _93132) (@lem6989422 A _93131 _93132 x' h1)). Qed.
Lemma lem6989425 {A : Type'} (_93131 : A -> nat) (_93132 : A -> nat) (_93133 : A -> Prop) (x' : type695 A) (h1 : term225 A x') : term504 A x' _93131 _93132 _93133.
Proof. exact (@lem6989424 A _93131 _93132 x' h1 _93133). Qed.
Lemma lem6989426 {A : Type'} (x' : type695 A) (_93131 : A -> nat) (_93133 : A -> Prop) (_93132 : A -> nat) : (term504 A x' _93131 _93132 _93133) = (term492 A x' _93131 _93133 _93132).
Proof. exact (eq_refl (term504 A x' _93131 _93132 _93133)). Qed.
Lemma lem6989427 {A : Type'} (_93131 : A -> nat) (_93133 : A -> Prop) (_93132 : A -> nat) (x' : type695 A) (h1 : term225 A x') : term492 A x' _93131 _93133 _93132.
Proof. exact (EQ_MP (@lem6989426 A x' _93131 _93133 _93132) (@lem6989425 A _93131 _93132 _93133 x' h1)). Qed.
Lemma lem6989437 {A : Type'} (_93137 : A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term505 A t f g _93137.
Proof. exact (@lem6989390 A s f t g h1 _93137). Qed.
Lemma lem6989438 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) (_93137 : A) : (term505 A t f g _93137) = (term457 A t f g _93137).
Proof. exact (eq_refl (term505 A t f g _93137)). Qed.
Lemma lem6989440 {A : Type'} (_93138 : A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term506 A s t f _93138.
Proof. exact (@lem6989409 A s f t g h1 _93138). Qed.
Lemma lem6989441 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) (_93138 : A) : (term506 A s t f _93138) = (term454 A s t f _93138).
Proof. exact (eq_refl (term506 A s t f _93138)). Qed.
Lemma lem6989442 {A : Type'} (_93138 : A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term454 A s t f _93138.
Proof. exact (EQ_MP (@lem6989441 A s t f _93138) (@lem6989440 A _93138 s f t g h1)). Qed.
Lemma lem6989447 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) (x : type693 A) (h1 : term353 A x) : term478 A x _93130 _93129 _93128.
Proof. exact (proj2 (@lem6989418 A _93130 _93129 _93128 x h1)). Qed.
Lemma lem6989448 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) (x : type693 A) (h1 : term353 A x) : term480 A x _93130 _93129 _93128.
Proof. exact (proj1 (@lem6989418 A _93130 _93129 _93128 x h1)). Qed.
Lemma lem6989449 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) (x : type693 A) (h1 : term353 A x) : term507 A x _93130 _93129 _93128.
Proof. exact (proj2 (@lem6989448 A _93130 _93129 _93128 x h1)). Qed.
Lemma lem6989450 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) (x : type693 A) (h1 : term353 A x) : term508 A x _93130 _93129 _93128.
Proof. exact (proj1 (@lem6989448 A _93130 _93129 _93128 x h1)). Qed.
Lemma lem6989452 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term446 A s f t g.
Proof. exact (proj2 (@lem6989242 A s f t g h1)). Qed.
Lemma lem6989462 {A : Type'} (_93137 : A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term457 A t f g _93137.
Proof. exact (EQ_MP (@lem6989438 A t f g _93137) (@lem6989437 A _93137 s f t g h1)). Qed.
Lemma lem6989473 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) (_93138 : A) : (term454 A s t f _93138) = (term509 A s t f _93138).
Proof. exact (@lem6986999 (term450 A _93138 s) (term449 A _93138 t) ((@I (A -> nat) f _93138) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem6989474 {A : Type'} (_93138 : A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term509 A s t f _93138.
Proof. exact (EQ_MP (@lem6989473 A s t f _93138) (@lem6989442 A _93138 s f t g h1)). Qed.
Lemma lem6989492 {A : Type'} (_93131 : A -> nat) (_93133 : A -> Prop) (_93132 : A -> nat) (x' : type695 A) (h1 : term225 A x') : term510 A x' _93131 _93133 _93132.
Proof. exact (proj1 (@lem6989427 A _93131 _93133 _93132 x' h1)). Qed.
Lemma lem6989498 {A : Type'} (_93131 : A -> nat) (_93133 : A -> Prop) (_93132 : A -> nat) (x' : type695 A) (h1 : term225 A x') : term511 A x' _93131 _93133 _93132.
Proof. exact (proj2 (@lem6989427 A _93131 _93133 _93132 x' h1)). Qed.
Lemma lem6989509 {A : Type'} (x : type693 A) (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term478 A x _93130 _93129 _93128) = (term512 A x _93130 _93129 _93128).
Proof. exact (@lem6986999 (term392 A _93129 _93130) (term369 A x _93128 _93129 _93130) ((term357 A _93130 _93128) = (term357 A _93129 _93128))). Qed.
Lemma lem6989510 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) (x : type693 A) (h1 : term353 A x) : term512 A x _93130 _93129 _93128.
Proof. exact (EQ_MP (@lem6989509 A x _93130 _93129 _93128) (@lem6989447 A _93130 _93129 _93128 x h1)). Qed.
Lemma lem6989521 {A : Type'} (x : type693 A) (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term508 A x _93130 _93129 _93128) = (term513 A x _93130 _93129 _93128).
Proof. exact (@lem6986999 (term392 A _93129 _93130) (term382 A x _93128 _93129 _93130) ((term357 A _93130 _93128) = (term357 A _93129 _93128))). Qed.
Lemma lem6989522 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) (x : type693 A) (h1 : term353 A x) : term513 A x _93130 _93129 _93128.
Proof. exact (EQ_MP (@lem6989521 A x _93130 _93129 _93128) (@lem6989450 A _93130 _93129 _93128 x h1)). Qed.
Lemma lem6989533 {A : Type'} (x : type693 A) (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term507 A x _93130 _93129 _93128) = (term514 A x _93130 _93129 _93128).
Proof. exact (@lem6986999 (term392 A _93129 _93130) (term378 A x _93128 _93130 _93129) ((term357 A _93130 _93128) = (term357 A _93129 _93128))). Qed.
Lemma lem6989534 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) (x : type693 A) (h1 : term353 A x) : term514 A x _93130 _93129 _93128.
Proof. exact (EQ_MP (@lem6989533 A x _93130 _93129 _93128) (@lem6989449 A _93130 _93129 _93128 x h1)). Qed.
Lemma lem6989844 (x : nat) (y : nat) (z : nat) : term515 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem6989894 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term391 A t s.
Proof. exact (proj1 (@lem6989245 A s f t g h1)). Qed.
Lemma lem6989895 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term516 A t s.
Proof. exact (fun h0 : term392 A t s => @lem6989894 A s f t g h1). Qed.
Lemma lem6989897 (p : Prop) : (term517 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6989898 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term516 A t s) = (term391 A t s).
Proof. exact (@lem6989897 (term391 A t s)). Qed.
Lemma lem6989899 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term391 A t s.
Proof. exact (EQ_MP (@lem6989898 A t s) (@lem6989895 A s f t g h1)). Qed.
Lemma lem6989901 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term391 A t s.
Proof. exact (proj1 (@lem6989245 A s f t g h1)). Qed.
Lemma lem6989902 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term516 A t s.
Proof. exact (fun h0 : term392 A t s => @lem6989901 A s f t g h1). Qed.
Lemma lem6989904 (p : Prop) : (term517 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6989905 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term516 A t s) = (term391 A t s).
Proof. exact (@lem6989904 (term391 A t s)). Qed.
Lemma lem6989906 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term391 A t s.
Proof. exact (EQ_MP (@lem6989905 A t s) (@lem6989902 A s f t g h1)). Qed.
Lemma lem6989909 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) (h1 : term518 A s t f) : term518 A s t f.
Proof. exact (h1). Qed.
Lemma lem6989910 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) (h1 : term518 A s t f) : term519 A s t f.
Proof. exact (fun h0 : (term357 A s f) = (term357 A t f) => @lem6989909 A s t f h1). Qed.
Lemma lem6989912 (p : Prop) : (term520 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6989913 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term519 A s t f) = (term518 A s t f).
Proof. exact (@lem6989912 ((term357 A s f) = (term357 A t f))). Qed.
Lemma lem6989914 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) (h1 : term518 A s t f) : term518 A s t f.
Proof. exact (EQ_MP (@lem6989913 A s t f) (@lem6989910 A s t f h1)). Qed.
Lemma lem6989920 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6989921 {A : Type'} (x : type693 A) (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term513 A x _93130 _93129 _93128) = (term521 A x _93130 _93129 _93128).
Proof. exact (@lem6989920 (term382 A x _93128 _93129 _93130) (term392 A _93129 _93130) ((term357 A _93130 _93128) = (term357 A _93129 _93128))). Qed.
Lemma lem6989935 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6989936 {A : Type'} (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term522 A _93130 _93129 _93128) = (term523 A _93128 _93129 _93130).
Proof. exact (@lem6989935 ((term357 A _93130 _93128) = (term357 A _93129 _93128)) (term392 A _93129 _93130)). Qed.
Lemma lem6989944 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term524 A x _93128 _93129 _93130) = (term524 A x _93128 _93129 _93130).
Proof. exact (eq_refl (term524 A x _93128 _93129 _93130)). Qed.
Lemma lem6989945 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term521 A x _93130 _93129 _93128) = (term525 A x _93128 _93129 _93130).
Proof. exact (MK_COMB (@lem6989944 A x _93128 _93129 _93130) (@lem6989936 A _93128 _93129 _93130)). Qed.
Lemma lem6989949 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6989950 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term525 A x _93128 _93129 _93130) = (term526 A x _93128 _93129 _93130).
Proof. exact (@lem6989949 ((term357 A _93130 _93128) = (term357 A _93129 _93128)) (term382 A x _93128 _93129 _93130) (term392 A _93129 _93130)). Qed.
Lemma lem6989968 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term521 A x _93130 _93129 _93128) = (term526 A x _93128 _93129 _93130).
Proof. exact (TRANS (@lem6989945 A x _93128 _93129 _93130) (@lem6989950 A x _93128 _93129 _93130)). Qed.
Lemma lem6989969 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term513 A x _93130 _93129 _93128) = (term526 A x _93128 _93129 _93130).
Proof. exact (TRANS (@lem6989921 A x _93130 _93129 _93128) (@lem6989968 A x _93128 _93129 _93130)). Qed.
Lemma lem6989970 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6989971 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term527 A x _93130 _93129 _93128) = (term528 A x _93128 _93129 _93130).
Proof. exact (MK_COMB (@lem6989970) (@lem6989969 A x _93128 _93129 _93130)). Qed.
Lemma lem6989985 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6989986 {A : Type'} (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term522 A _93130 _93129 _93128) = (term523 A _93128 _93129 _93130).
Proof. exact (@lem6989985 ((term357 A _93130 _93128) = (term357 A _93129 _93128)) (term392 A _93129 _93130)). Qed.
Lemma lem6989994 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term524 A x _93128 _93129 _93130) = (term524 A x _93128 _93129 _93130).
Proof. exact (eq_refl (term524 A x _93128 _93129 _93130)). Qed.
Lemma lem6989995 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term521 A x _93130 _93129 _93128) = (term525 A x _93128 _93129 _93130).
Proof. exact (MK_COMB (@lem6989994 A x _93128 _93129 _93130) (@lem6989986 A _93128 _93129 _93130)). Qed.
Lemma lem6989999 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6990000 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term525 A x _93128 _93129 _93130) = (term526 A x _93128 _93129 _93130).
Proof. exact (@lem6989999 ((term357 A _93130 _93128) = (term357 A _93129 _93128)) (term382 A x _93128 _93129 _93130) (term392 A _93129 _93130)). Qed.
Lemma lem6990018 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term521 A x _93130 _93129 _93128) = (term526 A x _93128 _93129 _93130).
Proof. exact (TRANS (@lem6989995 A x _93128 _93129 _93130) (@lem6990000 A x _93128 _93129 _93130)). Qed.
Lemma lem6990019 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : ((term513 A x _93130 _93129 _93128) = (term521 A x _93130 _93129 _93128)) = ((term526 A x _93128 _93129 _93130) = (term526 A x _93128 _93129 _93130)).
Proof. exact (MK_COMB (@lem6989971 A x _93128 _93129 _93130) (@lem6990018 A x _93128 _93129 _93130)). Qed.
Lemma lem6990021 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6990022 (x : Prop) : (x = x) = True.
Proof. exact (@lem6990021 Prop x). Qed.
Lemma lem6990023 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : ((term526 A x _93128 _93129 _93130) = (term526 A x _93128 _93129 _93130)) = True.
Proof. exact (@lem6990022 (term526 A x _93128 _93129 _93130)). Qed.
Lemma lem6990024 {A : Type'} (x : type693 A) (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : ((term513 A x _93130 _93129 _93128) = (term521 A x _93130 _93129 _93128)) = True.
Proof. exact (TRANS (@lem6990019 A x _93128 _93129 _93130) (@lem6990023 A x _93128 _93129 _93130)). Qed.
Lemma lem6990025 {A : Type'} (x : type693 A) (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : True = ((term513 A x _93130 _93129 _93128) = (term521 A x _93130 _93129 _93128)).
Proof. exact (SYM (@lem6990024 A x _93130 _93129 _93128)). Qed.
Lemma lem6990026 {A : Type'} (x : type693 A) (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term513 A x _93130 _93129 _93128) = (term521 A x _93130 _93129 _93128).
Proof. exact (EQ_MP (@lem6990025 A x _93130 _93129 _93128) (@lem0)). Qed.
Lemma lem6990027 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) (x : type693 A) (h1 : term353 A x) : term521 A x _93130 _93129 _93128.
Proof. exact (EQ_MP (@lem6990026 A x _93130 _93129 _93128) (@lem6989522 A _93130 _93129 _93128 x h1)). Qed.
Lemma lem6990029 (b : Prop) (a : Prop) : (a \/ b) = (term529 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6990030 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term521 A x _93130 _93129 _93128) = (term530 A x _93128 _93129 _93130).
Proof. exact (@lem6990029 (term522 A _93130 _93129 _93128) (term382 A x _93128 _93129 _93130)). Qed.
Lemma lem6990032 (a : Prop) (b : Prop) : (term531 a b) = (term532 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6990033 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term533 A _93130 _93129 _93128) = (term534 A _93130 _93129 _93128).
Proof. exact (@lem6990032 (term392 A _93129 _93130) ((term357 A _93130 _93128) = (term357 A _93129 _93128))). Qed.
Lemma lem6990035 (a : Prop) : (term535 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6990036 {A : Type'} (_93129 : A -> Prop) (_93130 : A -> Prop) : (term536 A _93129 _93130) = (term391 A _93129 _93130).
Proof. exact (@lem6990035 (term391 A _93129 _93130)). Qed.
Lemma lem6990037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6990038 {A : Type'} (_93129 : A -> Prop) (_93130 : A -> Prop) : (term537 A _93129 _93130) = (term462 A _93129 _93130).
Proof. exact (MK_COMB (@lem6990037) (@lem6990036 A _93129 _93130)). Qed.
Lemma lem6990039 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term518 A _93130 _93129 _93128) = (term518 A _93130 _93129 _93128).
Proof. exact (eq_refl (term518 A _93130 _93129 _93128)). Qed.
Lemma lem6990040 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term534 A _93130 _93129 _93128) = (term538 A _93130 _93129 _93128).
Proof. exact (MK_COMB (@lem6990038 A _93129 _93130) (@lem6990039 A _93130 _93129 _93128)). Qed.
Lemma lem6990041 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term533 A _93130 _93129 _93128) = (term538 A _93130 _93129 _93128).
Proof. exact (TRANS (@lem6990033 A _93130 _93129 _93128) (@lem6990040 A _93130 _93129 _93128)). Qed.
Lemma lem6990042 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6990043 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term539 A _93130 _93129 _93128) = (term540 A _93130 _93129 _93128).
Proof. exact (MK_COMB (@lem6990042) (@lem6990041 A _93130 _93129 _93128)). Qed.
Lemma lem6990044 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term382 A x _93128 _93129 _93130) = (term382 A x _93128 _93129 _93130).
Proof. exact (eq_refl (term382 A x _93128 _93129 _93130)). Qed.
Lemma lem6990045 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term530 A x _93128 _93129 _93130) = (term541 A x _93128 _93129 _93130).
Proof. exact (MK_COMB (@lem6990043 A _93130 _93129 _93128) (@lem6990044 A x _93128 _93129 _93130)). Qed.
Lemma lem6990046 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term521 A x _93130 _93129 _93128) = (term541 A x _93128 _93129 _93130).
Proof. exact (TRANS (@lem6990030 A x _93128 _93129 _93130) (@lem6990045 A x _93128 _93129 _93130)). Qed.
Lemma lem6990048 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term518 A s t f) (h2 : term88 A s f t g) : term538 A s t f.
Proof. exact (conj (@lem6989906 A s f t g h2) (@lem6989914 A s t f h1)). Qed.
Lemma lem6990050 {A : Type'} (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) (x : type693 A) (h1 : term353 A x) : term541 A x _93128 _93129 _93130.
Proof. exact (EQ_MP (@lem6990046 A x _93128 _93129 _93130) (@lem6990027 A _93130 _93129 _93128 x h1)). Qed.
Lemma lem6990051 {A : Type'} (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) (x : type693 A) (h1 : term353 A x) : term541 A x _93128 _93129 _93130.
Proof. exact (@lem6990050 A _93128 _93129 _93130 x h1). Qed.
Lemma lem6990052 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : A -> Prop) (x : type693 A) (h1 : term353 A x) : term541 A x f t s.
Proof. exact (@lem6990051 A f t s x h1). Qed.
Lemma lem6990055 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term518 A s t f) (h3 : term88 A s f t g) : term382 A x f t s.
Proof. exact (@lem6990052 A f t s x h1 (@lem6990048 A s f t g h2 h3)). Qed.
Lemma lem6990056 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term518 A s t f) (h3 : term88 A s f t g) : term542 A x f t s.
Proof. exact (fun h0 : term543 A x f t s => @lem6990055 A x s f t g h1 h2 h3). Qed.
Lemma lem6990058 (p : Prop) : (term517 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6990059 {A : Type'} (x : type693 A) (f : A -> nat) (t : A -> Prop) (s : A -> Prop) : (term542 A x f t s) = (term382 A x f t s).
Proof. exact (@lem6990058 (term382 A x f t s)). Qed.
Lemma lem6990060 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term518 A s t f) (h3 : term88 A s f t g) : term382 A x f t s.
Proof. exact (EQ_MP (@lem6990059 A x f t s) (@lem6990056 A x s f t g h1 h2 h3)). Qed.
Lemma lem6990062 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term391 A t s.
Proof. exact (proj1 (@lem6989245 A s f t g h1)). Qed.
Lemma lem6990063 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term516 A t s.
Proof. exact (fun h0 : term392 A t s => @lem6990062 A s f t g h1). Qed.
Lemma lem6990065 (p : Prop) : (term517 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6990066 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term516 A t s) = (term391 A t s).
Proof. exact (@lem6990065 (term391 A t s)). Qed.
Lemma lem6990067 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term391 A t s.
Proof. exact (EQ_MP (@lem6990066 A t s) (@lem6990063 A s f t g h1)). Qed.
Lemma lem6990070 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) (h1 : term518 A s t f) : term518 A s t f.
Proof. exact (h1). Qed.
Lemma lem6990071 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) (h1 : term518 A s t f) : term519 A s t f.
Proof. exact (fun h0 : (term357 A s f) = (term357 A t f) => @lem6990070 A s t f h1). Qed.
Lemma lem6990073 (p : Prop) : (term520 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6990074 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term519 A s t f) = (term518 A s t f).
Proof. exact (@lem6990073 ((term357 A s f) = (term357 A t f))). Qed.
Lemma lem6990075 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) (h1 : term518 A s t f) : term518 A s t f.
Proof. exact (EQ_MP (@lem6990074 A s t f) (@lem6990071 A s t f h1)). Qed.
Lemma lem6990081 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6990082 {A : Type'} (x : type693 A) (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term512 A x _93130 _93129 _93128) = (term544 A x _93130 _93129 _93128).
Proof. exact (@lem6990081 (term369 A x _93128 _93129 _93130) (term392 A _93129 _93130) ((term357 A _93130 _93128) = (term357 A _93129 _93128))). Qed.
Lemma lem6990098 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6990099 {A : Type'} (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term522 A _93130 _93129 _93128) = (term523 A _93128 _93129 _93130).
Proof. exact (@lem6990098 ((term357 A _93130 _93128) = (term357 A _93129 _93128)) (term392 A _93129 _93130)). Qed.
Lemma lem6990107 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term545 A x _93128 _93129 _93130) = (term545 A x _93128 _93129 _93130).
Proof. exact (eq_refl (term545 A x _93128 _93129 _93130)). Qed.
Lemma lem6990108 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term544 A x _93130 _93129 _93128) = (term546 A x _93128 _93129 _93130).
Proof. exact (MK_COMB (@lem6990107 A x _93128 _93129 _93130) (@lem6990099 A _93128 _93129 _93130)). Qed.
Lemma lem6990112 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6990113 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term546 A x _93128 _93129 _93130) = (term547 A x _93128 _93129 _93130).
Proof. exact (@lem6990112 ((term357 A _93130 _93128) = (term357 A _93129 _93128)) (term369 A x _93128 _93129 _93130) (term392 A _93129 _93130)). Qed.
Lemma lem6990133 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term544 A x _93130 _93129 _93128) = (term547 A x _93128 _93129 _93130).
Proof. exact (TRANS (@lem6990108 A x _93128 _93129 _93130) (@lem6990113 A x _93128 _93129 _93130)). Qed.
Lemma lem6990134 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term512 A x _93130 _93129 _93128) = (term547 A x _93128 _93129 _93130).
Proof. exact (TRANS (@lem6990082 A x _93130 _93129 _93128) (@lem6990133 A x _93128 _93129 _93130)). Qed.
Lemma lem6990135 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6990136 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term548 A x _93130 _93129 _93128) = (term549 A x _93128 _93129 _93130).
Proof. exact (MK_COMB (@lem6990135) (@lem6990134 A x _93128 _93129 _93130)). Qed.
Lemma lem6990152 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6990153 {A : Type'} (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term522 A _93130 _93129 _93128) = (term523 A _93128 _93129 _93130).
Proof. exact (@lem6990152 ((term357 A _93130 _93128) = (term357 A _93129 _93128)) (term392 A _93129 _93130)). Qed.
Lemma lem6990161 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term545 A x _93128 _93129 _93130) = (term545 A x _93128 _93129 _93130).
Proof. exact (eq_refl (term545 A x _93128 _93129 _93130)). Qed.
Lemma lem6990162 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term544 A x _93130 _93129 _93128) = (term546 A x _93128 _93129 _93130).
Proof. exact (MK_COMB (@lem6990161 A x _93128 _93129 _93130) (@lem6990153 A _93128 _93129 _93130)). Qed.
Lemma lem6990166 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6990167 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term546 A x _93128 _93129 _93130) = (term547 A x _93128 _93129 _93130).
Proof. exact (@lem6990166 ((term357 A _93130 _93128) = (term357 A _93129 _93128)) (term369 A x _93128 _93129 _93130) (term392 A _93129 _93130)). Qed.
Lemma lem6990187 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term544 A x _93130 _93129 _93128) = (term547 A x _93128 _93129 _93130).
Proof. exact (TRANS (@lem6990162 A x _93128 _93129 _93130) (@lem6990167 A x _93128 _93129 _93130)). Qed.
Lemma lem6990188 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : ((term512 A x _93130 _93129 _93128) = (term544 A x _93130 _93129 _93128)) = ((term547 A x _93128 _93129 _93130) = (term547 A x _93128 _93129 _93130)).
Proof. exact (MK_COMB (@lem6990136 A x _93128 _93129 _93130) (@lem6990187 A x _93128 _93129 _93130)). Qed.
Lemma lem6990190 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6990191 (x : Prop) : (x = x) = True.
Proof. exact (@lem6990190 Prop x). Qed.
Lemma lem6990192 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : ((term547 A x _93128 _93129 _93130) = (term547 A x _93128 _93129 _93130)) = True.
Proof. exact (@lem6990191 (term547 A x _93128 _93129 _93130)). Qed.
Lemma lem6990193 {A : Type'} (x : type693 A) (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : ((term512 A x _93130 _93129 _93128) = (term544 A x _93130 _93129 _93128)) = True.
Proof. exact (TRANS (@lem6990188 A x _93128 _93129 _93130) (@lem6990192 A x _93128 _93129 _93130)). Qed.
Lemma lem6990194 {A : Type'} (x : type693 A) (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : True = ((term512 A x _93130 _93129 _93128) = (term544 A x _93130 _93129 _93128)).
Proof. exact (SYM (@lem6990193 A x _93130 _93129 _93128)). Qed.
Lemma lem6990195 {A : Type'} (x : type693 A) (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term512 A x _93130 _93129 _93128) = (term544 A x _93130 _93129 _93128).
Proof. exact (EQ_MP (@lem6990194 A x _93130 _93129 _93128) (@lem0)). Qed.
Lemma lem6990196 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) (x : type693 A) (h1 : term353 A x) : term544 A x _93130 _93129 _93128.
Proof. exact (EQ_MP (@lem6990195 A x _93130 _93129 _93128) (@lem6989510 A _93130 _93129 _93128 x h1)). Qed.
Lemma lem6990198 (b : Prop) (a : Prop) : (a \/ b) = (term529 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6990199 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term544 A x _93130 _93129 _93128) = (term550 A x _93128 _93129 _93130).
Proof. exact (@lem6990198 (term522 A _93130 _93129 _93128) (term369 A x _93128 _93129 _93130)). Qed.
Lemma lem6990201 (a : Prop) (b : Prop) : (term531 a b) = (term532 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6990202 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term533 A _93130 _93129 _93128) = (term534 A _93130 _93129 _93128).
Proof. exact (@lem6990201 (term392 A _93129 _93130) ((term357 A _93130 _93128) = (term357 A _93129 _93128))). Qed.
Lemma lem6990204 (a : Prop) : (term535 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6990205 {A : Type'} (_93129 : A -> Prop) (_93130 : A -> Prop) : (term536 A _93129 _93130) = (term391 A _93129 _93130).
Proof. exact (@lem6990204 (term391 A _93129 _93130)). Qed.
Lemma lem6990206 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6990207 {A : Type'} (_93129 : A -> Prop) (_93130 : A -> Prop) : (term537 A _93129 _93130) = (term462 A _93129 _93130).
Proof. exact (MK_COMB (@lem6990206) (@lem6990205 A _93129 _93130)). Qed.
Lemma lem6990208 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term518 A _93130 _93129 _93128) = (term518 A _93130 _93129 _93128).
Proof. exact (eq_refl (term518 A _93130 _93129 _93128)). Qed.
Lemma lem6990209 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term534 A _93130 _93129 _93128) = (term538 A _93130 _93129 _93128).
Proof. exact (MK_COMB (@lem6990207 A _93129 _93130) (@lem6990208 A _93130 _93129 _93128)). Qed.
Lemma lem6990210 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term533 A _93130 _93129 _93128) = (term538 A _93130 _93129 _93128).
Proof. exact (TRANS (@lem6990202 A _93130 _93129 _93128) (@lem6990209 A _93130 _93129 _93128)). Qed.
Lemma lem6990211 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6990212 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term539 A _93130 _93129 _93128) = (term540 A _93130 _93129 _93128).
Proof. exact (MK_COMB (@lem6990211) (@lem6990210 A _93130 _93129 _93128)). Qed.
Lemma lem6990213 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term369 A x _93128 _93129 _93130) = (term369 A x _93128 _93129 _93130).
Proof. exact (eq_refl (term369 A x _93128 _93129 _93130)). Qed.
Lemma lem6990214 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term550 A x _93128 _93129 _93130) = (term551 A x _93128 _93129 _93130).
Proof. exact (MK_COMB (@lem6990212 A _93130 _93129 _93128) (@lem6990213 A x _93128 _93129 _93130)). Qed.
Lemma lem6990215 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term544 A x _93130 _93129 _93128) = (term551 A x _93128 _93129 _93130).
Proof. exact (TRANS (@lem6990199 A x _93128 _93129 _93130) (@lem6990214 A x _93128 _93129 _93130)). Qed.
Lemma lem6990217 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term518 A s t f) (h2 : term88 A s f t g) : term538 A s t f.
Proof. exact (conj (@lem6990067 A s f t g h2) (@lem6990075 A s t f h1)). Qed.
Lemma lem6990219 {A : Type'} (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) (x : type693 A) (h1 : term353 A x) : term551 A x _93128 _93129 _93130.
Proof. exact (EQ_MP (@lem6990215 A x _93128 _93129 _93130) (@lem6990196 A _93130 _93129 _93128 x h1)). Qed.
Lemma lem6990220 {A : Type'} (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) (x : type693 A) (h1 : term353 A x) : term551 A x _93128 _93129 _93130.
Proof. exact (@lem6990219 A _93128 _93129 _93130 x h1). Qed.
Lemma lem6990221 {A : Type'} (f : A -> nat) (t : A -> Prop) (s : A -> Prop) (x : type693 A) (h1 : term353 A x) : term551 A x f t s.
Proof. exact (@lem6990220 A f t s x h1). Qed.
Lemma lem6990224 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term518 A s t f) (h3 : term88 A s f t g) : term369 A x f t s.
Proof. exact (@lem6990221 A f t s x h1 (@lem6990217 A s f t g h2 h3)). Qed.
Lemma lem6990225 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term518 A s t f) (h3 : term88 A s f t g) : term552 A x f t s.
Proof. exact (fun h0 : (term365 A x f t s) = (@I (nat -> nat) NUMERAL 0) => @lem6990224 A x s f t g h1 h2 h3). Qed.
Lemma lem6990227 (p : Prop) : (term520 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6990228 {A : Type'} (x : type693 A) (f : A -> nat) (t : A -> Prop) (s : A -> Prop) : (term552 A x f t s) = (term369 A x f t s).
Proof. exact (@lem6990227 ((term365 A x f t s) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem6990229 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term518 A s t f) (h3 : term88 A s f t g) : term369 A x f t s.
Proof. exact (EQ_MP (@lem6990228 A x f t s) (@lem6990225 A x s f t g h1 h2 h3)). Qed.
Lemma lem6990235 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6990236 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> nat) (_93138 : A) : (term509 A s t f _93138) = (term553 A t s f _93138).
Proof. exact (@lem6990235 (term449 A _93138 t) (term450 A _93138 s) ((@I (A -> nat) f _93138) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem6990250 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6990251 {A : Type'} (f : A -> nat) (_93138 : A) (s : A -> Prop) : (term554 A s f _93138) = (term555 A f _93138 s).
Proof. exact (@lem6990250 ((@I (A -> nat) f _93138) = (@I (nat -> nat) NUMERAL 0)) (term450 A _93138 s)). Qed.
Lemma lem6990259 {A : Type'} (_93138 : A) (t : A -> Prop) : (term556 A _93138 t) = (term556 A _93138 t).
Proof. exact (eq_refl (term556 A _93138 t)). Qed.
Lemma lem6990260 {A : Type'} (t : A -> Prop) (f : A -> nat) (_93138 : A) (s : A -> Prop) : (term553 A t s f _93138) = (term557 A t f _93138 s).
Proof. exact (MK_COMB (@lem6990259 A _93138 t) (@lem6990251 A f _93138 s)). Qed.
Lemma lem6990264 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6990265 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93138 : A) (s : A -> Prop) : (term557 A t f _93138 s) = (term558 A f t _93138 s).
Proof. exact (@lem6990264 ((@I (A -> nat) f _93138) = (@I (nat -> nat) NUMERAL 0)) (term449 A _93138 t) (term450 A _93138 s)). Qed.
Lemma lem6990283 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93138 : A) (s : A -> Prop) : (term553 A t s f _93138) = (term558 A f t _93138 s).
Proof. exact (TRANS (@lem6990260 A t f _93138 s) (@lem6990265 A f t _93138 s)). Qed.
Lemma lem6990284 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93138 : A) (s : A -> Prop) : (term509 A s t f _93138) = (term558 A f t _93138 s).
Proof. exact (TRANS (@lem6990236 A t s f _93138) (@lem6990283 A f t _93138 s)). Qed.
Lemma lem6990285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6990286 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93138 : A) (s : A -> Prop) : (term559 A s t f _93138) = (term560 A f t _93138 s).
Proof. exact (MK_COMB (@lem6990285) (@lem6990284 A f t _93138 s)). Qed.
Lemma lem6990300 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6990301 {A : Type'} (f : A -> nat) (_93138 : A) (s : A -> Prop) : (term554 A s f _93138) = (term555 A f _93138 s).
Proof. exact (@lem6990300 ((@I (A -> nat) f _93138) = (@I (nat -> nat) NUMERAL 0)) (term450 A _93138 s)). Qed.
Lemma lem6990309 {A : Type'} (_93138 : A) (t : A -> Prop) : (term556 A _93138 t) = (term556 A _93138 t).
Proof. exact (eq_refl (term556 A _93138 t)). Qed.
Lemma lem6990310 {A : Type'} (t : A -> Prop) (f : A -> nat) (_93138 : A) (s : A -> Prop) : (term553 A t s f _93138) = (term557 A t f _93138 s).
Proof. exact (MK_COMB (@lem6990309 A _93138 t) (@lem6990301 A f _93138 s)). Qed.
Lemma lem6990314 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6990315 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93138 : A) (s : A -> Prop) : (term557 A t f _93138 s) = (term558 A f t _93138 s).
Proof. exact (@lem6990314 ((@I (A -> nat) f _93138) = (@I (nat -> nat) NUMERAL 0)) (term449 A _93138 t) (term450 A _93138 s)). Qed.
Lemma lem6990333 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93138 : A) (s : A -> Prop) : (term553 A t s f _93138) = (term558 A f t _93138 s).
Proof. exact (TRANS (@lem6990310 A t f _93138 s) (@lem6990315 A f t _93138 s)). Qed.
Lemma lem6990334 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93138 : A) (s : A -> Prop) : ((term509 A s t f _93138) = (term553 A t s f _93138)) = ((term558 A f t _93138 s) = (term558 A f t _93138 s)).
Proof. exact (MK_COMB (@lem6990286 A f t _93138 s) (@lem6990333 A f t _93138 s)). Qed.
Lemma lem6990336 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6990337 (x : Prop) : (x = x) = True.
Proof. exact (@lem6990336 Prop x). Qed.
Lemma lem6990338 {A : Type'} (f : A -> nat) (t : A -> Prop) (_93138 : A) (s : A -> Prop) : ((term558 A f t _93138 s) = (term558 A f t _93138 s)) = True.
Proof. exact (@lem6990337 (term558 A f t _93138 s)). Qed.
Lemma lem6990339 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> nat) (_93138 : A) : ((term509 A s t f _93138) = (term553 A t s f _93138)) = True.
Proof. exact (TRANS (@lem6990334 A f t _93138 s) (@lem6990338 A f t _93138 s)). Qed.
Lemma lem6990340 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> nat) (_93138 : A) : True = ((term509 A s t f _93138) = (term553 A t s f _93138)).
Proof. exact (SYM (@lem6990339 A t s f _93138)). Qed.
Lemma lem6990341 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> nat) (_93138 : A) : (term509 A s t f _93138) = (term553 A t s f _93138).
Proof. exact (EQ_MP (@lem6990340 A t s f _93138) (@lem0)). Qed.
Lemma lem6990342 {A : Type'} (_93138 : A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term553 A t s f _93138.
Proof. exact (EQ_MP (@lem6990341 A t s f _93138) (@lem6989474 A _93138 s f t g h1)). Qed.
Lemma lem6990344 (b : Prop) (a : Prop) : (a \/ b) = (term529 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6990345 {A : Type'} (s : A -> Prop) (f : A -> nat) (_93138 : A) (t : A -> Prop) : (term553 A t s f _93138) = (term561 A s f _93138 t).
Proof. exact (@lem6990344 (term554 A s f _93138) (term449 A _93138 t)). Qed.
Lemma lem6990347 (a : Prop) (b : Prop) : (term531 a b) = (term532 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6990348 {A : Type'} (s : A -> Prop) (f : A -> nat) (_93138 : A) : (term562 A s f _93138) = (term563 A s f _93138).
Proof. exact (@lem6990347 (term450 A _93138 s) ((@I (A -> nat) f _93138) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem6990350 (a : Prop) : (term535 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6990351 {A : Type'} (_93138 : A) (s : A -> Prop) : (term564 A _93138 s) = (term449 A _93138 s).
Proof. exact (@lem6990350 (term449 A _93138 s)). Qed.
Lemma lem6990352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6990353 {A : Type'} (_93138 : A) (s : A -> Prop) : (term565 A _93138 s) = (term566 A _93138 s).
Proof. exact (MK_COMB (@lem6990352) (@lem6990351 A _93138 s)). Qed.
Lemma lem6990354 {A : Type'} (f : A -> nat) (_93138 : A) : (term567 A f _93138) = (term567 A f _93138).
Proof. exact (eq_refl (term567 A f _93138)). Qed.
Lemma lem6990355 {A : Type'} (s : A -> Prop) (f : A -> nat) (_93138 : A) : (term563 A s f _93138) = (term568 A s f _93138).
Proof. exact (MK_COMB (@lem6990353 A _93138 s) (@lem6990354 A f _93138)). Qed.
Lemma lem6990356 {A : Type'} (s : A -> Prop) (f : A -> nat) (_93138 : A) : (term562 A s f _93138) = (term568 A s f _93138).
Proof. exact (TRANS (@lem6990348 A s f _93138) (@lem6990355 A s f _93138)). Qed.
Lemma lem6990357 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6990358 {A : Type'} (s : A -> Prop) (f : A -> nat) (_93138 : A) : (term569 A s f _93138) = (term570 A s f _93138).
Proof. exact (MK_COMB (@lem6990357) (@lem6990356 A s f _93138)). Qed.
Lemma lem6990359 {A : Type'} (_93138 : A) (t : A -> Prop) : (term449 A _93138 t) = (term449 A _93138 t).
Proof. exact (eq_refl (term449 A _93138 t)). Qed.
Lemma lem6990360 {A : Type'} (s : A -> Prop) (f : A -> nat) (_93138 : A) (t : A -> Prop) : (term561 A s f _93138 t) = (term571 A s f _93138 t).
Proof. exact (MK_COMB (@lem6990358 A s f _93138) (@lem6990359 A _93138 t)). Qed.
Lemma lem6990361 {A : Type'} (s : A -> Prop) (f : A -> nat) (_93138 : A) (t : A -> Prop) : (term553 A t s f _93138) = (term571 A s f _93138 t).
Proof. exact (TRANS (@lem6990345 A s f _93138 t) (@lem6990360 A s f _93138 t)). Qed.
Lemma lem6990363 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term518 A s t f) (h3 : term88 A s f t g) : term572 A x f t s.
Proof. exact (conj (@lem6990060 A x s f t g h1 h2 h3) (@lem6990229 A x s f t g h1 h2 h3)). Qed.
Lemma lem6990365 {A : Type'} (_93138 : A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term571 A s f _93138 t.
Proof. exact (EQ_MP (@lem6990361 A s f _93138 t) (@lem6990342 A _93138 s f t g h1)). Qed.
Lemma lem6990366 {A : Type'} (_93138 : A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term571 A s f _93138 t.
Proof. exact (@lem6990365 A _93138 s f t g h1). Qed.
Lemma lem6990367 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term573 A x f s t.
Proof. exact (@lem6990366 A (term362 A x f t s) s f t g h1). Qed.
Lemma lem6990370 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term518 A s t f) (h3 : term88 A s f t g) : term376 A x f s t.
Proof. exact (@lem6990367 A x s f t g h3 (@lem6990363 A x s f t g h1 h2 h3)). Qed.
Lemma lem6990371 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term518 A s t f) (h3 : term88 A s f t g) : term574 A x f s t.
Proof. exact (fun h0 : term378 A x f s t => @lem6990370 A x s f t g h1 h2 h3). Qed.
Lemma lem6990373 (p : Prop) : (term517 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6990374 {A : Type'} (x : type693 A) (f : A -> nat) (s : A -> Prop) (t : A -> Prop) : (term574 A x f s t) = (term376 A x f s t).
Proof. exact (@lem6990373 (term376 A x f s t)). Qed.
Lemma lem6990375 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term518 A s t f) (h3 : term88 A s f t g) : term376 A x f s t.
Proof. exact (EQ_MP (@lem6990374 A x f s t) (@lem6990371 A x s f t g h1 h2 h3)). Qed.
Lemma lem6990381 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6990382 {A : Type'} (x : type693 A) (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term514 A x _93130 _93129 _93128) = (term575 A x _93130 _93129 _93128).
Proof. exact (@lem6990381 (term378 A x _93128 _93130 _93129) (term392 A _93129 _93130) ((term357 A _93130 _93128) = (term357 A _93129 _93128))). Qed.
Lemma lem6990396 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6990397 {A : Type'} (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term522 A _93130 _93129 _93128) = (term523 A _93128 _93129 _93130).
Proof. exact (@lem6990396 ((term357 A _93130 _93128) = (term357 A _93129 _93128)) (term392 A _93129 _93130)). Qed.
Lemma lem6990405 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93130 : A -> Prop) (_93129 : A -> Prop) : (term576 A x _93128 _93130 _93129) = (term576 A x _93128 _93130 _93129).
Proof. exact (eq_refl (term576 A x _93128 _93130 _93129)). Qed.
Lemma lem6990406 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term575 A x _93130 _93129 _93128) = (term577 A x _93128 _93129 _93130).
Proof. exact (MK_COMB (@lem6990405 A x _93128 _93130 _93129) (@lem6990397 A _93128 _93129 _93130)). Qed.
Lemma lem6990410 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6990411 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term577 A x _93128 _93129 _93130) = (term578 A x _93128 _93129 _93130).
Proof. exact (@lem6990410 ((term357 A _93130 _93128) = (term357 A _93129 _93128)) (term378 A x _93128 _93130 _93129) (term392 A _93129 _93130)). Qed.
Lemma lem6990429 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term575 A x _93130 _93129 _93128) = (term578 A x _93128 _93129 _93130).
Proof. exact (TRANS (@lem6990406 A x _93128 _93129 _93130) (@lem6990411 A x _93128 _93129 _93130)). Qed.
Lemma lem6990430 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term514 A x _93130 _93129 _93128) = (term578 A x _93128 _93129 _93130).
Proof. exact (TRANS (@lem6990382 A x _93130 _93129 _93128) (@lem6990429 A x _93128 _93129 _93130)). Qed.
Lemma lem6990431 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6990432 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term579 A x _93130 _93129 _93128) = (term580 A x _93128 _93129 _93130).
Proof. exact (MK_COMB (@lem6990431) (@lem6990430 A x _93128 _93129 _93130)). Qed.
Lemma lem6990448 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6990449 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term482 A x _93128 _93130 _93129) = (term581 A x _93128 _93129 _93130).
Proof. exact (@lem6990448 (term378 A x _93128 _93130 _93129) (term392 A _93129 _93130)). Qed.
Lemma lem6990455 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term582 A _93130 _93129 _93128) = (term582 A _93130 _93129 _93128).
Proof. exact (eq_refl (term582 A _93130 _93129 _93128)). Qed.
Lemma lem6990456 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : (term583 A x _93128 _93130 _93129) = (term578 A x _93128 _93129 _93130).
Proof. exact (MK_COMB (@lem6990455 A _93130 _93129 _93128) (@lem6990449 A x _93128 _93129 _93130)). Qed.
Lemma lem6990467 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : ((term514 A x _93130 _93129 _93128) = (term583 A x _93128 _93130 _93129)) = ((term578 A x _93128 _93129 _93130) = (term578 A x _93128 _93129 _93130)).
Proof. exact (MK_COMB (@lem6990432 A x _93128 _93129 _93130) (@lem6990456 A x _93128 _93129 _93130)). Qed.
Lemma lem6990469 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6990470 (x : Prop) : (x = x) = True.
Proof. exact (@lem6990469 Prop x). Qed.
Lemma lem6990471 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93129 : A -> Prop) (_93130 : A -> Prop) : ((term578 A x _93128 _93129 _93130) = (term578 A x _93128 _93129 _93130)) = True.
Proof. exact (@lem6990470 (term578 A x _93128 _93129 _93130)). Qed.
Lemma lem6990472 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93130 : A -> Prop) (_93129 : A -> Prop) : ((term514 A x _93130 _93129 _93128) = (term583 A x _93128 _93130 _93129)) = True.
Proof. exact (TRANS (@lem6990467 A x _93128 _93129 _93130) (@lem6990471 A x _93128 _93129 _93130)). Qed.
Lemma lem6990473 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93130 : A -> Prop) (_93129 : A -> Prop) : True = ((term514 A x _93130 _93129 _93128) = (term583 A x _93128 _93130 _93129)).
Proof. exact (SYM (@lem6990472 A x _93128 _93130 _93129)). Qed.
Lemma lem6990474 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93130 : A -> Prop) (_93129 : A -> Prop) : (term514 A x _93130 _93129 _93128) = (term583 A x _93128 _93130 _93129).
Proof. exact (EQ_MP (@lem6990473 A x _93128 _93130 _93129) (@lem0)). Qed.
Lemma lem6990475 {A : Type'} (_93128 : A -> nat) (_93130 : A -> Prop) (_93129 : A -> Prop) (x : type693 A) (h1 : term353 A x) : term583 A x _93128 _93130 _93129.
Proof. exact (EQ_MP (@lem6990474 A x _93128 _93130 _93129) (@lem6989534 A _93130 _93129 _93128 x h1)). Qed.
Lemma lem6990477 (b : Prop) (a : Prop) : (a \/ b) = (term529 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6990478 {A : Type'} (x : type693 A) (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term583 A x _93128 _93130 _93129) = (term584 A x _93130 _93129 _93128).
Proof. exact (@lem6990477 (term482 A x _93128 _93130 _93129) ((term357 A _93130 _93128) = (term357 A _93129 _93128))). Qed.
Lemma lem6990480 (a : Prop) (b : Prop) : (term531 a b) = (term532 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6990481 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93130 : A -> Prop) (_93129 : A -> Prop) : (term585 A x _93128 _93130 _93129) = (term586 A x _93128 _93130 _93129).
Proof. exact (@lem6990480 (term392 A _93129 _93130) (term378 A x _93128 _93130 _93129)). Qed.
Lemma lem6990483 (a : Prop) : (term535 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6990484 {A : Type'} (_93129 : A -> Prop) (_93130 : A -> Prop) : (term536 A _93129 _93130) = (term391 A _93129 _93130).
Proof. exact (@lem6990483 (term391 A _93129 _93130)). Qed.
Lemma lem6990485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6990486 {A : Type'} (_93129 : A -> Prop) (_93130 : A -> Prop) : (term537 A _93129 _93130) = (term462 A _93129 _93130).
Proof. exact (MK_COMB (@lem6990485) (@lem6990484 A _93129 _93130)). Qed.
Lemma lem6990488 (a : Prop) : (term535 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6990489 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93130 : A -> Prop) (_93129 : A -> Prop) : (term587 A x _93128 _93130 _93129) = (term376 A x _93128 _93130 _93129).
Proof. exact (@lem6990488 (term376 A x _93128 _93130 _93129)). Qed.
Lemma lem6990490 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93130 : A -> Prop) (_93129 : A -> Prop) : (term586 A x _93128 _93130 _93129) = (term588 A x _93128 _93130 _93129).
Proof. exact (MK_COMB (@lem6990486 A _93129 _93130) (@lem6990489 A x _93128 _93130 _93129)). Qed.
Lemma lem6990491 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93130 : A -> Prop) (_93129 : A -> Prop) : (term585 A x _93128 _93130 _93129) = (term588 A x _93128 _93130 _93129).
Proof. exact (TRANS (@lem6990481 A x _93128 _93130 _93129) (@lem6990490 A x _93128 _93130 _93129)). Qed.
Lemma lem6990492 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6990493 {A : Type'} (x : type693 A) (_93128 : A -> nat) (_93130 : A -> Prop) (_93129 : A -> Prop) : (term589 A x _93128 _93130 _93129) = (term590 A x _93128 _93130 _93129).
Proof. exact (MK_COMB (@lem6990492) (@lem6990491 A x _93128 _93130 _93129)). Qed.
Lemma lem6990494 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : ((term357 A _93130 _93128) = (term357 A _93129 _93128)) = ((term357 A _93130 _93128) = (term357 A _93129 _93128)).
Proof. exact (eq_refl ((term357 A _93130 _93128) = (term357 A _93129 _93128))). Qed.
Lemma lem6990495 {A : Type'} (x : type693 A) (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term584 A x _93130 _93129 _93128) = (term591 A x _93130 _93129 _93128).
Proof. exact (MK_COMB (@lem6990493 A x _93128 _93130 _93129) (@lem6990494 A _93130 _93129 _93128)). Qed.
Lemma lem6990496 {A : Type'} (x : type693 A) (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) : (term583 A x _93128 _93130 _93129) = (term591 A x _93130 _93129 _93128).
Proof. exact (TRANS (@lem6990478 A x _93130 _93129 _93128) (@lem6990495 A x _93130 _93129 _93128)). Qed.
Lemma lem6990498 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term518 A s t f) (h3 : term88 A s f t g) : term588 A x f s t.
Proof. exact (conj (@lem6989899 A s f t g h3) (@lem6990375 A x s f t g h1 h2 h3)). Qed.
Lemma lem6990500 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) (x : type693 A) (h1 : term353 A x) : term591 A x _93130 _93129 _93128.
Proof. exact (EQ_MP (@lem6990496 A x _93130 _93129 _93128) (@lem6990475 A _93128 _93130 _93129 x h1)). Qed.
Lemma lem6990501 {A : Type'} (_93130 : A -> Prop) (_93129 : A -> Prop) (_93128 : A -> nat) (x : type693 A) (h1 : term353 A x) : term591 A x _93130 _93129 _93128.
Proof. exact (@lem6990500 A _93130 _93129 _93128 x h1). Qed.
Lemma lem6990502 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) (x : type693 A) (h1 : term353 A x) : term591 A x s t f.
Proof. exact (@lem6990501 A s t f x h1). Qed.
Lemma lem6990505 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term518 A s t f) (h3 : term88 A s f t g) : (term357 A s f) = (term357 A t f).
Proof. exact (@lem6990502 A s t f x h1 (@lem6990498 A x s f t g h1 h2 h3)). Qed.
Lemma lem6990506 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term88 A s f t g) : term592 A s t f.
Proof. exact (fun h0 : term518 A s t f => @lem6990505 A x s f t g h1 h0 h2). Qed.
Lemma lem6990508 (p : Prop) : (term517 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6990509 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term592 A s t f) = ((term357 A s f) = (term357 A t f)).
Proof. exact (@lem6990508 ((term357 A s f) = (term357 A t f))). Qed.
Lemma lem6990510 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term88 A s f t g) : (term357 A s f) = (term357 A t f).
Proof. exact (EQ_MP (@lem6990509 A s t f) (@lem6990506 A x s f t g h1 h2)). Qed.
Lemma lem6990512 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem6990513 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term357 A s f) = (term357 A s f).
Proof. exact (@lem6990512 (term357 A s f)). Qed.
Lemma lem6990514 {A : Type'} (s : A -> Prop) (f : A -> nat) : term593 A s f.
Proof. exact (fun h0 : term594 A s f => @lem6990513 A s f). Qed.
Lemma lem6990516 (p : Prop) : (term517 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6990517 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term593 A s f) = ((term357 A s f) = (term357 A s f)).
Proof. exact (@lem6990516 ((term357 A s f) = (term357 A s f))). Qed.
Lemma lem6990518 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term357 A s f) = (term357 A s f).
Proof. exact (EQ_MP (@lem6990517 A s f) (@lem6990514 A s f)). Qed.
Lemma lem6990536 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6990537 (y : nat) (x : nat) (z : nat) : (term595 x y z) = (term596 y x z).
Proof. exact (@lem6990536 (y = z) (term597 x z)). Qed.
Lemma lem6990547 (x : nat) (y : nat) : (term598 x y) = (term598 x y).
Proof. exact (eq_refl (term598 x y)). Qed.
Lemma lem6990548 (y : nat) (x : nat) (z : nat) : (term515 x y z) = (term599 y x z).
Proof. exact (MK_COMB (@lem6990547 x y) (@lem6990537 y x z)). Qed.
Lemma lem6990552 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6990553 (y : nat) (x : nat) (z : nat) : (term599 y x z) = (term600 y x z).
Proof. exact (@lem6990552 (y = z) (term597 x y) (term597 x z)). Qed.
Lemma lem6990575 (y : nat) (x : nat) (z : nat) : (term515 x y z) = (term600 y x z).
Proof. exact (TRANS (@lem6990548 y x z) (@lem6990553 y x z)). Qed.
Lemma lem6990576 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6990577 (y : nat) (x : nat) (z : nat) : (term601 x y z) = (term602 y x z).
Proof. exact (MK_COMB (@lem6990576) (@lem6990575 y x z)). Qed.
Lemma lem6990599 (y : nat) (x : nat) (z : nat) : (term600 y x z) = (term600 y x z).
Proof. exact (eq_refl (term600 y x z)). Qed.
Lemma lem6990600 (y : nat) (x : nat) (z : nat) : ((term515 x y z) = (term600 y x z)) = ((term600 y x z) = (term600 y x z)).
Proof. exact (MK_COMB (@lem6990577 y x z) (@lem6990599 y x z)). Qed.
Lemma lem6990602 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6990603 (x : Prop) : (x = x) = True.
Proof. exact (@lem6990602 Prop x). Qed.
Lemma lem6990604 (y : nat) (x : nat) (z : nat) : ((term600 y x z) = (term600 y x z)) = True.
Proof. exact (@lem6990603 (term600 y x z)). Qed.
Lemma lem6990605 (y : nat) (x : nat) (z : nat) : ((term515 x y z) = (term600 y x z)) = True.
Proof. exact (TRANS (@lem6990600 y x z) (@lem6990604 y x z)). Qed.
Lemma lem6990606 (y : nat) (x : nat) (z : nat) : True = ((term515 x y z) = (term600 y x z)).
Proof. exact (SYM (@lem6990605 y x z)). Qed.
Lemma lem6990607 (y : nat) (x : nat) (z : nat) : (term515 x y z) = (term600 y x z).
Proof. exact (EQ_MP (@lem6990606 y x z) (@lem0)). Qed.
Lemma lem6990608 (y : nat) (x : nat) (z : nat) : term600 y x z.
Proof. exact (EQ_MP (@lem6990607 y x z) (@lem6989844 x y z)). Qed.
Lemma lem6990610 (b : Prop) (a : Prop) : (a \/ b) = (term529 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6990611 (x : nat) (y : nat) (z : nat) : (term600 y x z) = (term603 x y z).
Proof. exact (@lem6990610 (term604 y x z) (y = z)). Qed.
Lemma lem6990613 (a : Prop) (b : Prop) : (term531 a b) = (term532 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6990614 (y : nat) (x : nat) (z : nat) : (term605 y x z) = (term606 y x z).
Proof. exact (@lem6990613 (term597 x y) (term597 x z)). Qed.
Lemma lem6990616 (a : Prop) : (term535 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6990617 (x : nat) (y : nat) : (term607 x y) = (x = y).
Proof. exact (@lem6990616 (x = y)). Qed.
Lemma lem6990618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6990619 (x : nat) (y : nat) : (term608 x y) = (term609 x y).
Proof. exact (MK_COMB (@lem6990618) (@lem6990617 x y)). Qed.
Lemma lem6990621 (a : Prop) : (term535 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6990622 (x : nat) (z : nat) : (term607 x z) = (x = z).
Proof. exact (@lem6990621 (x = z)). Qed.
Lemma lem6990623 (y : nat) (x : nat) (z : nat) : (term606 y x z) = (term610 y x z).
Proof. exact (MK_COMB (@lem6990619 x y) (@lem6990622 x z)). Qed.
Lemma lem6990624 (y : nat) (x : nat) (z : nat) : (term605 y x z) = (term610 y x z).
Proof. exact (TRANS (@lem6990614 y x z) (@lem6990623 y x z)). Qed.
Lemma lem6990625 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6990626 (y : nat) (x : nat) (z : nat) : (term611 y x z) = (term612 y x z).
Proof. exact (MK_COMB (@lem6990625) (@lem6990624 y x z)). Qed.
Lemma lem6990627 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem6990628 (x : nat) (y : nat) (z : nat) : (term603 x y z) = (term613 x y z).
Proof. exact (MK_COMB (@lem6990626 y x z) (@lem6990627 y z)). Qed.
Lemma lem6990629 (x : nat) (y : nat) (z : nat) : (term600 y x z) = (term613 x y z).
Proof. exact (TRANS (@lem6990611 x y z) (@lem6990628 x y z)). Qed.
Lemma lem6990631 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term88 A s f t g) : term614 A t s f.
Proof. exact (conj (@lem6990510 A x s f t g h1 h2) (@lem6990518 A s f)). Qed.
Lemma lem6990633 (x : nat) (y : nat) (z : nat) : term613 x y z.
Proof. exact (EQ_MP (@lem6990629 x y z) (@lem6990608 y x z)). Qed.
Lemma lem6990634 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> nat) : term615 A t s f.
Proof. exact (@lem6990633 (term357 A s f) (term357 A t f) (term357 A s f)). Qed.
Lemma lem6990637 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term88 A s f t g) : (term357 A t f) = (term357 A s f).
Proof. exact (@lem6990634 A t s f (@lem6990631 A x s f t g h1 h2)). Qed.
Lemma lem6990638 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term88 A s f t g) : term592 A t s f.
Proof. exact (fun h0 : term518 A t s f => @lem6990637 A x s f t g h1 h2). Qed.
Lemma lem6990640 (p : Prop) : (term517 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6990641 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> nat) : (term592 A t s f) = ((term357 A t f) = (term357 A s f)).
Proof. exact (@lem6990640 ((term357 A t f) = (term357 A s f))). Qed.
Lemma lem6990642 {A : Type'} (x : type693 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term88 A s f t g) : (term357 A t f) = (term357 A s f).
Proof. exact (EQ_MP (@lem6990641 A t s f) (@lem6990638 A x s f t g h1 h2)). Qed.
Lemma lem6990645 {A : Type'} (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term616 A f t g) : term616 A f t g.
Proof. exact (h1). Qed.
Lemma lem6990646 {A : Type'} (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term616 A f t g) : term617 A f t g.
Proof. exact (fun h0 : (term357 A t f) = (term357 A t g) => @lem6990645 A f t g h1). Qed.
Lemma lem6990648 (p : Prop) : (term520 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6990649 {A : Type'} (f : A -> nat) (t : A -> Prop) (g : A -> nat) : (term617 A f t g) = (term616 A f t g).
Proof. exact (@lem6990648 ((term357 A t f) = (term357 A t g))). Qed.
Lemma lem6990650 {A : Type'} (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term616 A f t g) : term616 A f t g.
Proof. exact (EQ_MP (@lem6990649 A f t g) (@lem6990646 A f t g h1)). Qed.
Lemma lem6990652 (b : Prop) (a : Prop) : (a \/ b) = (term529 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6990655 {A : Type'} (x' : type695 A) (_93131 : A -> nat) (_93132 : A -> nat) (_93133 : A -> Prop) : (term510 A x' _93131 _93133 _93132) = (term618 A x' _93131 _93132 _93133).
Proof. exact (@lem6990652 ((term357 A _93133 _93131) = (term357 A _93133 _93132)) (term428 A x' _93131 _93132 _93133)). Qed.
Lemma lem6990658 {A : Type'} (_93131 : A -> nat) (_93132 : A -> nat) (_93133 : A -> Prop) (x' : type695 A) (h1 : term225 A x') : term618 A x' _93131 _93132 _93133.
Proof. exact (EQ_MP (@lem6990655 A x' _93131 _93132 _93133) (@lem6989492 A _93131 _93133 _93132 x' h1)). Qed.
Lemma lem6990659 {A : Type'} (_93131 : A -> nat) (_93132 : A -> nat) (_93133 : A -> Prop) (x' : type695 A) (h1 : term225 A x') : term618 A x' _93131 _93132 _93133.
Proof. exact (@lem6990658 A _93131 _93132 _93133 x' h1). Qed.
Lemma lem6990660 {A : Type'} (f : A -> nat) (g : A -> nat) (t : A -> Prop) (x' : type695 A) (h1 : term225 A x') : term618 A x' f g t.
Proof. exact (@lem6990659 A f g t x' h1). Qed.
Lemma lem6990663 {A : Type'} (x' : type695 A) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term225 A x') (h2 : term616 A f t g) : term428 A x' f g t.
Proof. exact (@lem6990660 A f g t x' h1 (@lem6990650 A f t g h2)). Qed.
Lemma lem6990664 {A : Type'} (x' : type695 A) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term225 A x') (h2 : term616 A f t g) : term619 A x' f g t.
Proof. exact (fun h0 : term620 A x' f g t => @lem6990663 A x' f t g h1 h2). Qed.
Lemma lem6990666 (p : Prop) : (term517 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6990667 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (t : A -> Prop) : (term619 A x' f g t) = (term428 A x' f g t).
Proof. exact (@lem6990666 (term428 A x' f g t)). Qed.
Lemma lem6990668 {A : Type'} (x' : type695 A) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term225 A x') (h2 : term616 A f t g) : term428 A x' f g t.
Proof. exact (EQ_MP (@lem6990667 A x' f g t) (@lem6990664 A x' f t g h1 h2)). Qed.
Lemma lem6990674 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6990675 {A : Type'} (f : A -> nat) (g : A -> nat) (_93137 : A) (t : A -> Prop) : (term457 A t f g _93137) = (term621 A f g _93137 t).
Proof. exact (@lem6990674 ((@I (A -> nat) f _93137) = (@I (A -> nat) g _93137)) (term450 A _93137 t)). Qed.
Lemma lem6990683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6990684 {A : Type'} (f : A -> nat) (g : A -> nat) (_93137 : A) (t : A -> Prop) : (term622 A t f g _93137) = (term623 A f g _93137 t).
Proof. exact (MK_COMB (@lem6990683) (@lem6990675 A f g _93137 t)). Qed.
Lemma lem6990692 {A : Type'} (f : A -> nat) (g : A -> nat) (_93137 : A) (t : A -> Prop) : (term621 A f g _93137 t) = (term621 A f g _93137 t).
Proof. exact (eq_refl (term621 A f g _93137 t)). Qed.
Lemma lem6990693 {A : Type'} (f : A -> nat) (g : A -> nat) (_93137 : A) (t : A -> Prop) : ((term457 A t f g _93137) = (term621 A f g _93137 t)) = ((term621 A f g _93137 t) = (term621 A f g _93137 t)).
Proof. exact (MK_COMB (@lem6990684 A f g _93137 t) (@lem6990692 A f g _93137 t)). Qed.
Lemma lem6990695 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6990696 (x : Prop) : (x = x) = True.
Proof. exact (@lem6990695 Prop x). Qed.
Lemma lem6990697 {A : Type'} (f : A -> nat) (g : A -> nat) (_93137 : A) (t : A -> Prop) : ((term621 A f g _93137 t) = (term621 A f g _93137 t)) = True.
Proof. exact (@lem6990696 (term621 A f g _93137 t)). Qed.
Lemma lem6990698 {A : Type'} (f : A -> nat) (g : A -> nat) (_93137 : A) (t : A -> Prop) : ((term457 A t f g _93137) = (term621 A f g _93137 t)) = True.
Proof. exact (TRANS (@lem6990693 A f g _93137 t) (@lem6990697 A f g _93137 t)). Qed.
Lemma lem6990699 {A : Type'} (f : A -> nat) (g : A -> nat) (_93137 : A) (t : A -> Prop) : True = ((term457 A t f g _93137) = (term621 A f g _93137 t)).
Proof. exact (SYM (@lem6990698 A f g _93137 t)). Qed.
Lemma lem6990700 {A : Type'} (f : A -> nat) (g : A -> nat) (_93137 : A) (t : A -> Prop) : (term457 A t f g _93137) = (term621 A f g _93137 t).
Proof. exact (EQ_MP (@lem6990699 A f g _93137 t) (@lem0)). Qed.
Lemma lem6990701 {A : Type'} (_93137 : A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term621 A f g _93137 t.
Proof. exact (EQ_MP (@lem6990700 A f g _93137 t) (@lem6989462 A _93137 s f t g h1)). Qed.
Lemma lem6990703 (b : Prop) (a : Prop) : (a \/ b) = (term529 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6990704 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) (_93137 : A) : (term621 A f g _93137 t) = (term624 A t f g _93137).
Proof. exact (@lem6990703 (term450 A _93137 t) ((@I (A -> nat) f _93137) = (@I (A -> nat) g _93137))). Qed.
Lemma lem6990706 (a : Prop) : (term535 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6990707 {A : Type'} (_93137 : A) (t : A -> Prop) : (term564 A _93137 t) = (term449 A _93137 t).
Proof. exact (@lem6990706 (term449 A _93137 t)). Qed.
Lemma lem6990708 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6990709 {A : Type'} (_93137 : A) (t : A -> Prop) : (term625 A _93137 t) = (term626 A _93137 t).
Proof. exact (MK_COMB (@lem6990708) (@lem6990707 A _93137 t)). Qed.
Lemma lem6990710 {A : Type'} (f : A -> nat) (g : A -> nat) (_93137 : A) : ((@I (A -> nat) f _93137) = (@I (A -> nat) g _93137)) = ((@I (A -> nat) f _93137) = (@I (A -> nat) g _93137)).
Proof. exact (eq_refl ((@I (A -> nat) f _93137) = (@I (A -> nat) g _93137))). Qed.
Lemma lem6990711 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) (_93137 : A) : (term624 A t f g _93137) = (term627 A t f g _93137).
Proof. exact (MK_COMB (@lem6990709 A _93137 t) (@lem6990710 A f g _93137)). Qed.
Lemma lem6990712 {A : Type'} (t : A -> Prop) (f : A -> nat) (g : A -> nat) (_93137 : A) : (term621 A f g _93137 t) = (term627 A t f g _93137).
Proof. exact (TRANS (@lem6990704 A t f g _93137) (@lem6990711 A t f g _93137)). Qed.
Lemma lem6990715 {A : Type'} (_93137 : A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term627 A t f g _93137.
Proof. exact (EQ_MP (@lem6990712 A t f g _93137) (@lem6990701 A _93137 s f t g h1)). Qed.
Lemma lem6990716 {A : Type'} (_93137 : A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term627 A t f g _93137.
Proof. exact (@lem6990715 A _93137 s f t g h1). Qed.
Lemma lem6990717 {A : Type'} (x' : type695 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term628 A x' f g t.
Proof. exact (@lem6990716 A (term411 A x' f g t) s f t g h1). Qed.
Lemma lem6990720 {A : Type'} (x' : type695 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term225 A x') (h2 : term616 A f t g) (h3 : term88 A s f t g) : (term414 A x' f g t) = (term417 A x' f g t).
Proof. exact (@lem6990717 A x' s f t g h3 (@lem6990668 A x' f t g h1 h2)). Qed.
Lemma lem6990721 {A : Type'} (x' : type695 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term225 A x') (h2 : term616 A f t g) (h3 : term88 A s f t g) : term629 A x' f g t.
Proof. exact (fun h0 : term421 A x' f g t => @lem6990720 A x' s f t g h1 h2 h3). Qed.
Lemma lem6990723 (p : Prop) : (term517 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6990724 {A : Type'} (x' : type695 A) (f : A -> nat) (g : A -> nat) (t : A -> Prop) : (term629 A x' f g t) = ((term414 A x' f g t) = (term417 A x' f g t)).
Proof. exact (@lem6990723 ((term414 A x' f g t) = (term417 A x' f g t))). Qed.
Lemma lem6990725 {A : Type'} (x' : type695 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term225 A x') (h2 : term616 A f t g) (h3 : term88 A s f t g) : (term414 A x' f g t) = (term417 A x' f g t).
Proof. exact (EQ_MP (@lem6990724 A x' f g t) (@lem6990721 A x' s f t g h1 h2 h3)). Qed.
Lemma lem6990731 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6990732 {A : Type'} (x' : type695 A) (_93131 : A -> nat) (_93132 : A -> nat) (_93133 : A -> Prop) : (term511 A x' _93131 _93133 _93132) = (term630 A x' _93131 _93132 _93133).
Proof. exact (@lem6990731 ((term357 A _93133 _93131) = (term357 A _93133 _93132)) (term421 A x' _93131 _93132 _93133)). Qed.
Lemma lem6990742 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6990743 {A : Type'} (x' : type695 A) (_93131 : A -> nat) (_93132 : A -> nat) (_93133 : A -> Prop) : (term631 A x' _93131 _93133 _93132) = (term632 A x' _93131 _93132 _93133).
Proof. exact (MK_COMB (@lem6990742) (@lem6990732 A x' _93131 _93132 _93133)). Qed.
Lemma lem6990753 {A : Type'} (x' : type695 A) (_93131 : A -> nat) (_93132 : A -> nat) (_93133 : A -> Prop) : (term630 A x' _93131 _93132 _93133) = (term630 A x' _93131 _93132 _93133).
Proof. exact (eq_refl (term630 A x' _93131 _93132 _93133)). Qed.
Lemma lem6990754 {A : Type'} (x' : type695 A) (_93131 : A -> nat) (_93132 : A -> nat) (_93133 : A -> Prop) : ((term511 A x' _93131 _93133 _93132) = (term630 A x' _93131 _93132 _93133)) = ((term630 A x' _93131 _93132 _93133) = (term630 A x' _93131 _93132 _93133)).
Proof. exact (MK_COMB (@lem6990743 A x' _93131 _93132 _93133) (@lem6990753 A x' _93131 _93132 _93133)). Qed.
Lemma lem6990756 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6990757 (x : Prop) : (x = x) = True.
Proof. exact (@lem6990756 Prop x). Qed.
Lemma lem6990758 {A : Type'} (x' : type695 A) (_93131 : A -> nat) (_93132 : A -> nat) (_93133 : A -> Prop) : ((term630 A x' _93131 _93132 _93133) = (term630 A x' _93131 _93132 _93133)) = True.
Proof. exact (@lem6990757 (term630 A x' _93131 _93132 _93133)). Qed.
Lemma lem6990759 {A : Type'} (x' : type695 A) (_93131 : A -> nat) (_93132 : A -> nat) (_93133 : A -> Prop) : ((term511 A x' _93131 _93133 _93132) = (term630 A x' _93131 _93132 _93133)) = True.
Proof. exact (TRANS (@lem6990754 A x' _93131 _93132 _93133) (@lem6990758 A x' _93131 _93132 _93133)). Qed.
Lemma lem6990760 {A : Type'} (x' : type695 A) (_93131 : A -> nat) (_93132 : A -> nat) (_93133 : A -> Prop) : True = ((term511 A x' _93131 _93133 _93132) = (term630 A x' _93131 _93132 _93133)).
Proof. exact (SYM (@lem6990759 A x' _93131 _93132 _93133)). Qed.
Lemma lem6990761 {A : Type'} (x' : type695 A) (_93131 : A -> nat) (_93132 : A -> nat) (_93133 : A -> Prop) : (term511 A x' _93131 _93133 _93132) = (term630 A x' _93131 _93132 _93133).
Proof. exact (EQ_MP (@lem6990760 A x' _93131 _93132 _93133) (@lem0)). Qed.
Lemma lem6990762 {A : Type'} (_93131 : A -> nat) (_93132 : A -> nat) (_93133 : A -> Prop) (x' : type695 A) (h1 : term225 A x') : term630 A x' _93131 _93132 _93133.
Proof. exact (EQ_MP (@lem6990761 A x' _93131 _93132 _93133) (@lem6989498 A _93131 _93133 _93132 x' h1)). Qed.
Lemma lem6990764 (b : Prop) (a : Prop) : (a \/ b) = (term529 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6990765 {A : Type'} (x' : type695 A) (_93131 : A -> nat) (_93133 : A -> Prop) (_93132 : A -> nat) : (term630 A x' _93131 _93132 _93133) = (term633 A x' _93131 _93133 _93132).
Proof. exact (@lem6990764 (term421 A x' _93131 _93132 _93133) ((term357 A _93133 _93131) = (term357 A _93133 _93132))). Qed.
Lemma lem6990767 (a : Prop) : (term535 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6990768 {A : Type'} (x' : type695 A) (_93131 : A -> nat) (_93132 : A -> nat) (_93133 : A -> Prop) : (term634 A x' _93131 _93132 _93133) = ((term414 A x' _93131 _93132 _93133) = (term417 A x' _93131 _93132 _93133)).
Proof. exact (@lem6990767 ((term414 A x' _93131 _93132 _93133) = (term417 A x' _93131 _93132 _93133))). Qed.
Lemma lem6990769 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6990770 {A : Type'} (x' : type695 A) (_93131 : A -> nat) (_93132 : A -> nat) (_93133 : A -> Prop) : (term635 A x' _93131 _93132 _93133) = (term636 A x' _93131 _93132 _93133).
Proof. exact (MK_COMB (@lem6990769) (@lem6990768 A x' _93131 _93132 _93133)). Qed.
Lemma lem6990771 {A : Type'} (_93131 : A -> nat) (_93133 : A -> Prop) (_93132 : A -> nat) : ((term357 A _93133 _93131) = (term357 A _93133 _93132)) = ((term357 A _93133 _93131) = (term357 A _93133 _93132)).
Proof. exact (eq_refl ((term357 A _93133 _93131) = (term357 A _93133 _93132))). Qed.
Lemma lem6990772 {A : Type'} (x' : type695 A) (_93131 : A -> nat) (_93133 : A -> Prop) (_93132 : A -> nat) : (term633 A x' _93131 _93133 _93132) = (term637 A x' _93131 _93133 _93132).
Proof. exact (MK_COMB (@lem6990770 A x' _93131 _93132 _93133) (@lem6990771 A _93131 _93133 _93132)). Qed.
Lemma lem6990773 {A : Type'} (x' : type695 A) (_93131 : A -> nat) (_93133 : A -> Prop) (_93132 : A -> nat) : (term630 A x' _93131 _93132 _93133) = (term637 A x' _93131 _93133 _93132).
Proof. exact (TRANS (@lem6990765 A x' _93131 _93133 _93132) (@lem6990772 A x' _93131 _93133 _93132)). Qed.
Lemma lem6990776 {A : Type'} (_93131 : A -> nat) (_93133 : A -> Prop) (_93132 : A -> nat) (x' : type695 A) (h1 : term225 A x') : term637 A x' _93131 _93133 _93132.
Proof. exact (EQ_MP (@lem6990773 A x' _93131 _93133 _93132) (@lem6990762 A _93131 _93132 _93133 x' h1)). Qed.
Lemma lem6990777 {A : Type'} (_93131 : A -> nat) (_93133 : A -> Prop) (_93132 : A -> nat) (x' : type695 A) (h1 : term225 A x') : term637 A x' _93131 _93133 _93132.
Proof. exact (@lem6990776 A _93131 _93133 _93132 x' h1). Qed.
Lemma lem6990778 {A : Type'} (f : A -> nat) (t : A -> Prop) (g : A -> nat) (x' : type695 A) (h1 : term225 A x') : term637 A x' f t g.
Proof. exact (@lem6990777 A f t g x' h1). Qed.
Lemma lem6990781 {A : Type'} (x' : type695 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term225 A x') (h2 : term616 A f t g) (h3 : term88 A s f t g) : (term357 A t f) = (term357 A t g).
Proof. exact (@lem6990778 A f t g x' h1 (@lem6990725 A x' s f t g h1 h2 h3)). Qed.
Lemma lem6990782 {A : Type'} (x' : type695 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term225 A x') (h2 : term88 A s f t g) : term638 A f t g.
Proof. exact (fun h0 : term616 A f t g => @lem6990781 A x' s f t g h1 h0 h2). Qed.
Lemma lem6990784 (p : Prop) : (term517 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6990785 {A : Type'} (f : A -> nat) (t : A -> Prop) (g : A -> nat) : (term638 A f t g) = ((term357 A t f) = (term357 A t g)).
Proof. exact (@lem6990784 ((term357 A t f) = (term357 A t g))). Qed.
Lemma lem6990786 {A : Type'} (x' : type695 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term225 A x') (h2 : term88 A s f t g) : (term357 A t f) = (term357 A t g).
Proof. exact (EQ_MP (@lem6990785 A f t g) (@lem6990782 A x' s f t g h1 h2)). Qed.
Lemma lem6990787 {A : Type'} (x : type693 A) (x' : type695 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term225 A x') (h3 : term88 A s f t g) : term639 A s f t g.
Proof. exact (conj (@lem6990642 A x s f t g h1 h3) (@lem6990786 A x' s f t g h2 h3)). Qed.
Lemma lem6990789 (x : nat) (y : nat) (z : nat) : term613 x y z.
Proof. exact (EQ_MP (@lem6990629 x y z) (@lem6990608 y x z)). Qed.
Lemma lem6990790 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) : term640 A s f t g.
Proof. exact (@lem6990789 (term357 A t f) (term357 A s f) (term357 A t g)). Qed.
Lemma lem6990793 {A : Type'} (x : type693 A) (x' : type695 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term225 A x') (h3 : term88 A s f t g) : (term357 A s f) = (term357 A t g).
Proof. exact (@lem6990790 A s f t g (@lem6990787 A x x' s f t g h1 h2 h3)). Qed.
Lemma lem6990794 {A : Type'} (x : type693 A) (x' : type695 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term225 A x') (h3 : term88 A s f t g) : term641 A s f t g.
Proof. exact (fun h0 : term446 A s f t g => @lem6990793 A x x' s f t g h1 h2 h3). Qed.
Lemma lem6990796 (p : Prop) : (term517 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6990797 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) : (term641 A s f t g) = ((term357 A s f) = (term357 A t g)).
Proof. exact (@lem6990796 ((term357 A s f) = (term357 A t g))). Qed.
Lemma lem6990798 {A : Type'} (x : type693 A) (x' : type695 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term225 A x') (h3 : term88 A s f t g) : (term357 A s f) = (term357 A t g).
Proof. exact (EQ_MP (@lem6990797 A s f t g) (@lem6990794 A x x' s f t g h1 h2 h3)). Qed.
Lemma lem6990801 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6990803 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) : (term446 A s f t g) = (term642 A s f t g).
Proof. exact (@lem6990801 ((term357 A s f) = (term357 A t g))). Qed.
Lemma lem6990806 {A : Type'} (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term88 A s f t g) : term642 A s f t g.
Proof. exact (EQ_MP (@lem6990803 A s f t g) (@lem6989452 A s f t g h1)). Qed.
Lemma lem6990809 {A : Type'} (x : type693 A) (x' : type695 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term225 A x') (h3 : term88 A s f t g) : False.
Proof. exact (@lem6990806 A s f t g h3 (@lem6990798 A x x' s f t g h1 h2 h3)). Qed.
Lemma lem6990810 {A : Type'} (x : type693 A) (x' : type695 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term225 A x') (h3 : term88 A s f t g) : term643.
Proof. exact (fun h0 : ~ False => @lem6990809 A x x' s f t g h1 h2 h3). Qed.
Lemma lem6990812 (p : Prop) : (term517 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6990813 : term643 = False.
Proof. exact (@lem6990812 False). Qed.
Lemma lem6990814 {A : Type'} (x : type693 A) (x' : type695 A) (s : A -> Prop) (f : A -> nat) (t : A -> Prop) (g : A -> nat) (h1 : term353 A x) (h2 : term225 A x') (h3 : term88 A s f t g) : False.
Proof. exact (EQ_MP (@lem6990813) (@lem6990810 A x x' s f t g h1 h2 h3)). Qed.
Lemma lem6990815 {A : Type'} (x : type693 A) (x' : type695 A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term353 A x) (h2 : term225 A x') (h3 : term98 A s f g) : False.
Proof. exact (ex_elim (@lem6988516 A s f g h3) (fun t : A -> Prop => fun h0 : term97 A s f g t => @lem6990814 A x x' s f t g h1 h2 h0)). Qed.
Lemma lem6990816 {A : Type'} (x : type693 A) (x' : type695 A) (f : A -> nat) (g : A -> nat) (h1 : term353 A x) (h2 : term225 A x') (h3 : term105 A f g) : False.
Proof. exact (ex_elim (@lem6988515 A f g h3) (fun s : A -> Prop => fun h0 : term104 A f g s => @lem6990815 A x x' s f g h1 h2 h0)). Qed.
Lemma lem6990817 {A : Type'} (x : type693 A) (x' : type695 A) (g : A -> nat) (h1 : term353 A x) (h2 : term225 A x') (h3 : term10 A g) : False.
Proof. exact (ex_elim (@lem6987678 A g h3) (fun f : A -> nat => fun h0 : term112 A g f => @lem6990816 A x x' f g h1 h2 h0)). Qed.
Lemma lem6990818 {_127166 A : Type'} (x : type693 A) (x' : type695 A) (g : A -> nat) (h1 : term12 _127166) (h2 : term353 A x) (h3 : term225 A x') (h4 : term10 A g) : False.
Proof. exact (ex_elim (@lem6987944 _127166 h1) (fun x'' : type695 _127166 => fun h0 : term227 _127166 x'' => @lem6990817 A x x' g h2 h3 h4)). Qed.
Lemma lem6990819 {_127166 A : Type'} (x : type693 A) (g : A -> nat) (h1 : term12 _127166) (h2 : term353 A x) (h3 : term12 A) (h4 : term10 A g) : False.
Proof. exact (ex_elim (@lem6988210 A h3) (fun x' : type695 A => fun h0 : term227 A x' => @lem6990818 _127166 A x x' g h1 h2 h0 h4)). Qed.
Lemma lem6990820 {_127166 A : Type'} (g : A -> nat) (h1 : term12 _127166) (h2 : term11 A) (h3 : term12 A) (h4 : term10 A g) : False.
Proof. exact (ex_elim (@lem6988511 A h2) (fun x : type693 A => fun h0 : term355 A x => @lem6990819 _127166 A x g h1 h0 h3 h4)). Qed.
Lemma lem6990821 {_127166 A : Type'} (g : A -> nat) (h1 : term12 _127166) (h2 : term12 A) (h3 : term10 A g) : term17 A.
Proof. exact (fun h0 : term11 A => @lem6990820 _127166 A g h1 h0 h2 h3). Qed.
Lemma lem6990822 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem69 (term11 A)). Qed.
Lemma lem6990823 {_127166 A : Type'} (g : A -> nat) (h1 : term12 _127166) (h2 : term12 A) (h3 : term10 A g) : term18 A.
Proof. exact (EQ_MP (@lem6990822 A) (@lem6990821 _127166 A g h1 h2 h3)). Qed.
Lemma lem6990824 {_127166 A : Type'} (g : A -> nat) (h1 : term12 _127166) (h2 : term10 A g) : term21 A.
Proof. exact (fun h0 : term12 A => @lem6990823 _127166 A g h1 h0 h2). Qed.
Lemma lem6990825 {_127166 A : Type'} (g : A -> nat) (h1 : term10 A g) : term23 _127166 A.
Proof. exact (fun h0 : term12 _127166 => @lem6990824 _127166 A g h0 h1). Qed.
Lemma lem6990826 {_127166 A : Type'} (g : A -> nat) : term25 _127166 A g.
Proof. exact (fun h0 : term10 A g => @lem6990825 _127166 A g h0). Qed.
Lemma lem6990831 {_127166 A : Type'} : term29 _127166 A.
Proof. exact (fun g : A -> nat => @lem6990826 _127166 A g). Qed.
Lemma lem6990832 {_127166 A : Type'} : term28 _127166 A.
Proof. exact (EQ_MP (@lem6987442 _127166 A) (@lem6990831 _127166 A)). Qed.
Lemma lem6990833 {_127166 A : Type'} (g : A -> nat) : term644 _127166 A g.
Proof. exact (@lem6990832 _127166 A g). Qed.
Lemma lem6990834 {_127166 A : Type'} (g : A -> nat) : (term644 _127166 A g) = (term13 _127166 A g).
Proof. exact (eq_refl (term644 _127166 A g)). Qed.
Lemma lem6990835 {_127166 A : Type'} (g : A -> nat) : term13 _127166 A g.
Proof. exact (EQ_MP (@lem6990834 _127166 A g) (@lem6990833 _127166 A g)). Qed.
Lemma lem6990837 {_127166 A : Type'} (g : A -> nat) : term13 _127166 A g.
Proof. exact (@lem6987025 _127166 A g (@lem6990835 _127166 A g)). Qed.
Lemma lem6990838 {_127166 A : Type'} (g : A -> nat) (h1 : term10 A g) : term22 _127166 A.
Proof. exact (@lem6990837 _127166 A g (@lem6987004 A g h1)). Qed.
Lemma lem6990839 {A : Type'} (g : A -> nat) (h1 : term10 A g) : term20 A.
Proof. exact (@lem6990838 Prop A g h1 (@lem6938831 Prop)). Qed.
Lemma lem6990840 {A : Type'} (g : A -> nat) (h1 : term10 A g) : term17 A.
Proof. exact (@lem6990839 A g h1 (@lem6987008 A)). Qed.
Lemma lem6990841 {A : Type'} (g : A -> nat) (h1 : term10 A g) : False.
Proof. exact (@lem6990840 A g h1 (@lem6987005 A)). Qed.
Lemma lem6990842 {A : Type'} (g : A -> nat) (h1 : term10 A g) : (term10 A g) = False.
Proof. exact (prop_ext (fun h2 : term10 A g => @lem6990841 A g h1) (fun h2 : False => @lem6987004 A g h1)). Qed.
Lemma lem6990843 {A : Type'} (g : A -> nat) (h1 : term10 A g) : False.
Proof. exact (EQ_MP (@lem6990842 A g h1) (@lem6987004 A g h1)). Qed.
Lemma lem6990844 {A : Type'} (g : A -> nat) : term9 A g.
Proof. exact (fun h0 : term10 A g => @lem6990843 A g h0). Qed.
Lemma lem6990845 {A : Type'} (g : A -> nat) : term8 A g.
Proof. exact (EQ_MP (@lem6987003 A g) (@lem6990844 A g)). Qed.
