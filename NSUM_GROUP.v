Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_GROUP_term_abbrevs.
Require Import NSUM_EQ_0_spec.
Require Import NSUM_IMAGE_GEN_spec.
Require Import NSUM_SUPERSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1820_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm7_spec.
Lemma lem6993168 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6993169 {A : Type'} (f : A -> nat) (h1 : term0 A) : term1 A f.
Proof. exact (@lem6993168 A h1 f). Qed.
Lemma lem6993170 {A : Type'} (f : A -> nat) : (term1 A f) = (term2 A f).
Proof. exact (eq_refl (term1 A f)). Qed.
Lemma lem6993171 {A : Type'} (f : A -> nat) (h1 : term0 A) : term2 A f.
Proof. exact (EQ_MP (@lem6993170 A f) (@lem6993169 A f h1)). Qed.
Lemma lem6993172 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term0 A) : term3 A f s.
Proof. exact (@lem6993171 A f h1 s). Qed.
Lemma lem6993173 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term3 A f s) = (term4 A s f).
Proof. exact (eq_refl (term3 A f s)). Qed.
Lemma lem6993174 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term0 A) : term4 A s f.
Proof. exact (EQ_MP (@lem6993173 A s f) (@lem6993172 A f s h1)). Qed.
Lemma lem6993175 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term5 A s f) : term5 A s f.
Proof. exact (h1). Qed.
Lemma lem6993176 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term5 A s f) (h2 : term0 A) : (@nsum A s f) = (NUMERAL 0).
Proof. exact (@lem6993174 A s f h2 (@lem6993175 A s f h1)). Qed.
Lemma lem6993177 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term5 A s f) : term6 A s f.
Proof. exact (fun h0 : term0 A => @lem6993176 A s f h1 h0). Qed.
Lemma lem6993178 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6993179 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term5 A s f) (h2 : term0 A) : (@nsum A s f) = (NUMERAL 0).
Proof. exact (@lem6993177 A s f h1 (@lem6993178 A h2)). Qed.
Lemma lem6993180 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term0 A) : term4 A s f.
Proof. exact (fun h0 : term5 A s f => @lem6993179 A s f h0 h1). Qed.
Lemma lem6993181 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term7 A s.
Proof. exact (fun f : A -> nat => @lem6993180 A s f h1). Qed.
Lemma lem6993182 {A : Type'} (h1 : term0 A) : term8 A.
Proof. exact (fun s : A -> Prop => @lem6993181 A s h1). Qed.
Lemma lem6993183 {A : Type'} : term9 A.
Proof. exact (fun h0 : term0 A => @lem6993182 A h0). Qed.
Lemma lem6993184 {A : Type'} : term8 A.
Proof. exact (@lem6993183 A (@lem6930973 A)). Qed.
Lemma lem6993185 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (@lem6993184 A s). Qed.
Lemma lem6993186 {A : Type'} (s : A -> Prop) : (term10 A s) = (term7 A s).
Proof. exact (eq_refl (term10 A s)). Qed.
Lemma lem6993187 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (EQ_MP (@lem6993186 A s) (@lem6993185 A s)). Qed.
Lemma lem6993188 {A : Type'} (s : A -> Prop) (f : A -> nat) : term11 A s f.
Proof. exact (@lem6993187 A s f). Qed.
Lemma lem6993189 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term11 A s f) = (term4 A s f).
Proof. exact (eq_refl (term11 A s f)). Qed.
Lemma lem6993191 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem6993192 {A : Type'} (f : A -> nat) (h1 : term12 A) : term13 A f.
Proof. exact (@lem6993191 A h1 f). Qed.
Lemma lem6993193 {A : Type'} (f : A -> nat) : (term13 A f) = (term14 A f).
Proof. exact (eq_refl (term13 A f)). Qed.
Lemma lem6993194 {A : Type'} (f : A -> nat) (h1 : term12 A) : term14 A f.
Proof. exact (EQ_MP (@lem6993193 A f) (@lem6993192 A f h1)). Qed.
Lemma lem6993195 {A : Type'} (f : A -> nat) (u : A -> Prop) (h1 : term12 A) : term15 A f u.
Proof. exact (@lem6993194 A f h1 u). Qed.
Lemma lem6993196 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term15 A f u) = (term16 A u f).
Proof. exact (eq_refl (term15 A f u)). Qed.
Lemma lem6993197 {A : Type'} (u : A -> Prop) (f : A -> nat) (h1 : term12 A) : term16 A u f.
Proof. exact (EQ_MP (@lem6993196 A u f) (@lem6993195 A f u h1)). Qed.
Lemma lem6993198 {A : Type'} (u : A -> Prop) (f : A -> nat) (v : A -> Prop) (h1 : term12 A) : term17 A u f v.
Proof. exact (@lem6993197 A u f h1 v). Qed.
Lemma lem6993199 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term17 A u f v) = (term18 A v u f).
Proof. exact (eq_refl (term17 A u f v)). Qed.
Lemma lem6993200 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term12 A) : term18 A v u f.
Proof. exact (EQ_MP (@lem6993199 A v u f) (@lem6993198 A u f v h1)). Qed.
Lemma lem6993201 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term19 A v u f) : term19 A v u f.
Proof. exact (h1). Qed.
Lemma lem6993202 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term12 A) (h2 : term19 A v u f) : (@nsum A v f) = (@nsum A u f).
Proof. exact (@lem6993200 A v u f h1 (@lem6993201 A v u f h2)). Qed.
Lemma lem6993203 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term19 A v u f) : term20 A v u f.
Proof. exact (fun h0 : term12 A => @lem6993202 A v u f h0 h1). Qed.
Lemma lem6993204 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem6993205 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term12 A) (h2 : term19 A v u f) : (@nsum A v f) = (@nsum A u f).
Proof. exact (@lem6993203 A v u f h2 (@lem6993204 A h1)). Qed.
Lemma lem6993206 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term12 A) : term18 A v u f.
Proof. exact (fun h0 : term19 A v u f => @lem6993205 A v u f h1 h0). Qed.
Lemma lem6993207 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term12 A) : term21 A v u.
Proof. exact (fun f : A -> nat => @lem6993206 A v u f h1). Qed.
Lemma lem6993208 {A : Type'} (v : A -> Prop) (h1 : term12 A) : term22 A v.
Proof. exact (fun u : A -> Prop => @lem6993207 A v u h1). Qed.
Lemma lem6993209 {A : Type'} (h1 : term12 A) : term23 A.
Proof. exact (fun v : A -> Prop => @lem6993208 A v h1). Qed.
Lemma lem6993210 {A : Type'} : term24 A.
Proof. exact (fun h0 : term12 A => @lem6993209 A h0). Qed.
Lemma lem6993211 {A : Type'} : term23 A.
Proof. exact (@lem6993210 A (@lem6962131 A)). Qed.
Lemma lem6993212 {A : Type'} (v : A -> Prop) : term25 A v.
Proof. exact (@lem6993211 A v). Qed.
Lemma lem6993213 {A : Type'} (v : A -> Prop) : (term25 A v) = (term22 A v).
Proof. exact (eq_refl (term25 A v)). Qed.
Lemma lem6993214 {A : Type'} (v : A -> Prop) : term22 A v.
Proof. exact (EQ_MP (@lem6993213 A v) (@lem6993212 A v)). Qed.
Lemma lem6993215 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term26 A v u.
Proof. exact (@lem6993214 A v u). Qed.
Lemma lem6993216 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term26 A v u) = (term21 A v u).
Proof. exact (eq_refl (term26 A v u)). Qed.
Lemma lem6993217 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term21 A v u.
Proof. exact (EQ_MP (@lem6993216 A v u) (@lem6993215 A v u)). Qed.
Lemma lem6993218 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term27 A v u f.
Proof. exact (@lem6993217 A v u f). Qed.
Lemma lem6993219 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term27 A v u f) = (term18 A v u f).
Proof. exact (eq_refl (term27 A v u f)). Qed.
Lemma lem6993221 {A B : Type'} : term28 A B.
Proof. exact (@lem6993167 A B). Qed.
Lemma lem6993222 {A B : Type'} (f : A -> B) : term29 A B f.
Proof. exact (@lem6993221 A B f). Qed.
Lemma lem6993223 {A B : Type'} (f : A -> B) : (term29 A B f) = (term30 A B f).
Proof. exact (eq_refl (term29 A B f)). Qed.
Lemma lem6993224 {A B : Type'} (f : A -> B) : term30 A B f.
Proof. exact (EQ_MP (@lem6993223 A B f) (@lem6993222 A B f)). Qed.
Lemma lem6993225 {A B : Type'} (f : A -> B) (g : A -> nat) : term31 A B f g.
Proof. exact (@lem6993224 A B f g). Qed.
Lemma lem6993226 {A B : Type'} (f : A -> B) (g : A -> nat) : (term31 A B f g) = (term32 A B f g).
Proof. exact (eq_refl (term31 A B f g)). Qed.
Lemma lem6993227 {A B : Type'} (f : A -> B) (g : A -> nat) : term32 A B f g.
Proof. exact (EQ_MP (@lem6993226 A B f g) (@lem6993225 A B f g)). Qed.
Lemma lem6993228 {A B : Type'} (f : A -> B) (g : A -> nat) (s : A -> Prop) : term33 A B f g s.
Proof. exact (@lem6993227 A B f g s). Qed.
Lemma lem6993229 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term33 A B f g s) = (term34 A B s f g).
Proof. exact (eq_refl (term33 A B f g s)). Qed.
Lemma lem6993230 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> nat) : term34 A B s f g.
Proof. exact (EQ_MP (@lem6993229 A B s f g) (@lem6993228 A B f g s)). Qed.
Lemma lem6993231 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term35 A B f s t) : term35 A B f s t.
Proof. exact (h1). Qed.
Lemma lem6993232 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term36 A B f s t) : term36 A B f s t.
Proof. exact (h1). Qed.
Lemma lem6993233 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6993234 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6993243 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6993234 A s) (@lem6993233 A s h1)). Qed.
Lemma lem6993244 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6993245 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term37 A s) = (imp True).
Proof. exact (MK_COMB (@lem6993244) (@lem6993243 A s h1)). Qed.
Lemma lem6993256 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> nat) : ((@nsum A s g) = (term38 A B s f g)) = ((@nsum A s g) = (term38 A B s f g)).
Proof. exact (eq_refl ((@nsum A s g) = (term38 A B s f g))). Qed.
Lemma lem6993257 {A B : Type'} (f : A -> B) (g : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : (term34 A B s f g) = (term39 A B s f g).
Proof. exact (MK_COMB (@lem6993245 A s h1) (@lem6993256 A B s f g)). Qed.
Lemma lem6993259 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem6993260 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term39 A B s f g) = ((@nsum A s g) = (term38 A B s f g)).
Proof. exact (@lem6993259 ((@nsum A s g) = (term38 A B s f g))). Qed.
Lemma lem6993271 {A B : Type'} (f : A -> B) (g : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : (term34 A B s f g) = ((@nsum A s g) = (term38 A B s f g)).
Proof. exact (TRANS (@lem6993257 A B f g s h1) (@lem6993260 A B s f g)). Qed.
Lemma lem6993272 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6993273 {A B : Type'} (f : A -> B) (g : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : (term40 A B s f g) = (term41 A B s f g).
Proof. exact (MK_COMB (@lem6993272) (@lem6993271 A B f g s h1)). Qed.
Lemma lem6993284 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (g : A -> nat) : ((term42 A B t s f g) = (@nsum A s g)) = ((term42 A B t s f g) = (@nsum A s g)).
Proof. exact (eq_refl ((term42 A B t s f g) = (@nsum A s g))). Qed.
Lemma lem6993285 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : (term43 A B t f s g) = (term44 A B t f s g).
Proof. exact (MK_COMB (@lem6993273 A B f g s h1) (@lem6993284 A B t f s g)). Qed.
Lemma lem6993290 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : (term44 A B t f s g) = (term43 A B t f s g).
Proof. exact (SYM (@lem6993285 A B t f g s h1)). Qed.
Lemma lem6993291 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> nat) (h1 : (@nsum A s g) = (term38 A B s f g)) : (@nsum A s g) = (term38 A B s f g).
Proof. exact (h1). Qed.
Lemma lem6993292 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term45 A B t s f g) = (term45 A B t s f g).
Proof. exact (eq_refl (term45 A B t s f g)). Qed.
Lemma lem6993293 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) (h1 : (@nsum A s g) = (term38 A B s f g)) : (term46 A B t f s g) = (term47 A B t s f g).
Proof. exact (MK_COMB (@lem6993292 A B t s f g) (@lem6993291 A B s f g h1)). Qed.
Lemma lem6993294 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term47 A B t s f g) = ((term42 A B t s f g) = (term38 A B s f g)).
Proof. exact (eq_refl (term47 A B t s f g)). Qed.
Lemma lem6993295 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (g : A -> nat) : (term48 A B t f s g) = (term48 A B t f s g).
Proof. exact (eq_refl (term48 A B t f s g)). Qed.
Lemma lem6993296 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : ((term46 A B t f s g) = (term47 A B t s f g)) = ((term46 A B t f s g) = ((term42 A B t s f g) = (term38 A B s f g))).
Proof. exact (MK_COMB (@lem6993295 A B t f s g) (@lem6993294 A B t s f g)). Qed.
Lemma lem6993297 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (g : A -> nat) : (term46 A B t f s g) = ((term42 A B t s f g) = (@nsum A s g)).
Proof. exact (eq_refl (term46 A B t f s g)). Qed.
Lemma lem6993298 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6993299 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (g : A -> nat) : (term48 A B t f s g) = (term49 A B t f s g).
Proof. exact (MK_COMB (@lem6993298) (@lem6993297 A B t f s g)). Qed.
Lemma lem6993300 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : ((term42 A B t s f g) = (term38 A B s f g)) = ((term42 A B t s f g) = (term38 A B s f g)).
Proof. exact (eq_refl ((term42 A B t s f g) = (term38 A B s f g))). Qed.
Lemma lem6993301 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : ((term46 A B t f s g) = ((term42 A B t s f g) = (term38 A B s f g))) = (((term42 A B t s f g) = (@nsum A s g)) = ((term42 A B t s f g) = (term38 A B s f g))).
Proof. exact (MK_COMB (@lem6993299 A B t f s g) (@lem6993300 A B t s f g)). Qed.
Lemma lem6993302 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : ((term46 A B t f s g) = (term47 A B t s f g)) = (((term42 A B t s f g) = (@nsum A s g)) = ((term42 A B t s f g) = (term38 A B s f g))).
Proof. exact (TRANS (@lem6993296 A B t s f g) (@lem6993301 A B t s f g)). Qed.
Lemma lem6993303 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) (h1 : (@nsum A s g) = (term38 A B s f g)) : ((term42 A B t s f g) = (@nsum A s g)) = ((term42 A B t s f g) = (term38 A B s f g)).
Proof. exact (EQ_MP (@lem6993302 A B t s f g) (@lem6993293 A B t s f g h1)). Qed.
Lemma lem6993304 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) (h1 : (@nsum A s g) = (term38 A B s f g)) : ((term42 A B t s f g) = (term38 A B s f g)) = ((term42 A B t s f g) = (@nsum A s g)).
Proof. exact (SYM (@lem6993303 A B t s f g h1)). Qed.
Lemma lem6993306 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term18 A v u f.
Proof. exact (EQ_MP (@lem6993219 A v u f) (@lem6993218 A v u f)). Qed.
Lemma lem6993307 {B : Type'} (v : B -> Prop) (u : B -> Prop) (f : B -> nat) : term18 B v u f.
Proof. exact (@lem6993306 B v u f). Qed.
Lemma lem6993308 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : term50 A B t s f g.
Proof. exact (@lem6993307 B t (@IMAGE A B f s) (term51 A B s f g)). Qed.
Lemma lem6993311 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term52 A B t s f g) = (term52 A B t s f g).
Proof. exact (eq_refl (term52 A B t s f g)). Qed.
Lemma lem6993312 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term52 A B t s f g) = (term50 A B t s f g).
Proof. exact (eq_refl (term52 A B t s f g)). Qed.
Lemma lem6993313 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term53 A B t s f g) = (term53 A B t s f g).
Proof. exact (eq_refl (term53 A B t s f g)). Qed.
Lemma lem6993314 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : ((term52 A B t s f g) = (term52 A B t s f g)) = ((term52 A B t s f g) = (term50 A B t s f g)).
Proof. exact (MK_COMB (@lem6993313 A B t s f g) (@lem6993312 A B t s f g)). Qed.
Lemma lem6993315 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term52 A B t s f g) = (term50 A B t s f g).
Proof. exact (eq_refl (term52 A B t s f g)). Qed.
Lemma lem6993316 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6993317 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term53 A B t s f g) = (term54 A B t s f g).
Proof. exact (MK_COMB (@lem6993316) (@lem6993315 A B t s f g)). Qed.
Lemma lem6993318 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term50 A B t s f g) = (term50 A B t s f g).
Proof. exact (eq_refl (term50 A B t s f g)). Qed.
Lemma lem6993319 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : ((term52 A B t s f g) = (term50 A B t s f g)) = ((term50 A B t s f g) = (term50 A B t s f g)).
Proof. exact (MK_COMB (@lem6993317 A B t s f g) (@lem6993318 A B t s f g)). Qed.
Lemma lem6993320 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : ((term52 A B t s f g) = (term52 A B t s f g)) = ((term50 A B t s f g) = (term50 A B t s f g)).
Proof. exact (TRANS (@lem6993314 A B t s f g) (@lem6993319 A B t s f g)). Qed.
Lemma lem6993321 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term50 A B t s f g) = (term50 A B t s f g).
Proof. exact (EQ_MP (@lem6993320 A B t s f g) (@lem6993311 A B t s f g)). Qed.
Lemma lem6993322 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : term50 A B t s f g.
Proof. exact (EQ_MP (@lem6993321 A B t s f g) (@lem6993308 A B t s f g)). Qed.
Lemma lem6993325 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term36 A B f s t) = ((term36 A B f s t) = True).
Proof. exact (@lem7 (term36 A B f s t)). Qed.
Lemma lem6993330 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term36 A B f s t) : (term36 A B f s t) = True.
Proof. exact (EQ_MP (@lem6993325 A B f s t) (@lem6993232 A B f s t h1)). Qed.
Lemma lem6993331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6993332 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term36 A B f s t) : (term55 A B f s t) = (and True).
Proof. exact (MK_COMB (@lem6993331) (@lem6993330 A B f s t h1)). Qed.
Lemma lem6993344 {A B : Type'} (f : A -> B) (y : A) : (term56 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6993345 {B : Type'} (f : B -> nat) (y : B) : (term57 B f y) = (f y).
Proof. exact (@lem6993344 B nat f y). Qed.
Lemma lem6993346 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> nat) (x : B) : (term58 A B s f g x) = (term59 A B s f g x).
Proof. exact (@lem6993345 B (term51 A B s f g) x). Qed.
Lemma lem6993347 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (g : A -> nat) : (term59 A B s f g y) = (term60 A B s f y g).
Proof. exact (eq_refl (term59 A B s f g y)). Qed.
Lemma lem6993348 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term61 A B s f g) = (term51 A B s f g).
Proof. exact (fun_ext (fun y : B => @lem6993347 A B s f y g)). Qed.
Lemma lem6993349 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6993350 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> nat) (x : B) : (term58 A B s f g x) = (term59 A B s f g x).
Proof. exact (MK_COMB (@lem6993348 A B s f g) (@lem6993349 B x)). Qed.
Lemma lem6993351 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6993352 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> nat) (x : B) : (term62 A B s f g x) = (term63 A B s f g x).
Proof. exact (MK_COMB (@lem6993351) (@lem6993350 A B s f g x)). Qed.
Lemma lem6993353 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term59 A B s f g x) = (term60 A B s f x g).
Proof. exact (eq_refl (term59 A B s f g x)). Qed.
Lemma lem6993354 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : ((term58 A B s f g x) = (term59 A B s f g x)) = ((term59 A B s f g x) = (term60 A B s f x g)).
Proof. exact (MK_COMB (@lem6993352 A B s f g x) (@lem6993353 A B s f x g)). Qed.
Lemma lem6993355 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term59 A B s f g x) = (term60 A B s f x g).
Proof. exact (EQ_MP (@lem6993354 A B s f x g) (@lem6993346 A B s f g x)). Qed.
Lemma lem6993364 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6993365 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term63 A B s f g x) = (term64 A B s f x g).
Proof. exact (MK_COMB (@lem6993364) (@lem6993355 A B s f x g)). Qed.
Lemma lem6993366 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem6993367 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : ((term59 A B s f g x) = (NUMERAL 0)) = ((term60 A B s f x g) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6993365 A B s f x g) (@lem6993366)). Qed.
Lemma lem6993370 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term65 A B t x f s) = (term65 A B t x f s).
Proof. exact (eq_refl (term65 A B t x f s)). Qed.
Lemma lem6993371 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term66 A B t s f g x) = (term67 A B t s f x g).
Proof. exact (MK_COMB (@lem6993370 A B t x f s) (@lem6993367 A B s f x g)). Qed.
Lemma lem6993374 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term68 A B t s f g) = (term69 A B t s f g).
Proof. exact (fun_ext (fun x : B => @lem6993371 A B t s f x g)). Qed.
Lemma lem6993375 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6993376 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term70 A B t s f g) = (term71 A B t s f g).
Proof. exact (MK_COMB (@lem6993375 B) (@lem6993374 A B t s f g)). Qed.
Lemma lem6993381 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term36 A B f s t) : (term72 A B t s f g) = (term73 A B t s f g).
Proof. exact (MK_COMB (@lem6993332 A B f s t h1) (@lem6993376 A B t s f g)). Qed.
Lemma lem6993383 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6993384 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term73 A B t s f g) = (term71 A B t s f g).
Proof. exact (@lem6993383 (term71 A B t s f g)). Qed.
Lemma lem6993403 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term36 A B f s t) : (term72 A B t s f g) = (term71 A B t s f g).
Proof. exact (TRANS (@lem6993381 A B g f s t h1) (@lem6993384 A B t s f g)). Qed.
Lemma lem6993404 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term36 A B f s t) : (term71 A B t s f g) = (term72 A B t s f g).
Proof. exact (SYM (@lem6993403 A B g f s t h1)). Qed.
Lemma lem6993405 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term74 A B t x f s) : term74 A B t x f s.
Proof. exact (h1). Qed.
Lemma lem6993406 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (h1 : term75 A B x f s) : term75 A B x f s.
Proof. exact (h1). Qed.
Lemma lem6993407 {B : Type'} (x : B) (t : B -> Prop) (h1 : @IN B x t) : @IN B x t.
Proof. exact (h1). Qed.
Lemma lem6993409 {A : Type'} (s : A -> Prop) (f : A -> nat) : term4 A s f.
Proof. exact (EQ_MP (@lem6993189 A s f) (@lem6993188 A s f)). Qed.
Lemma lem6993410 {A : Type'} (s : A -> Prop) (f : A -> nat) : term4 A s f.
Proof. exact (@lem6993409 A s f). Qed.
Lemma lem6993411 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : term76 A B s f x g.
Proof. exact (@lem6993410 A (term77 A B s f x) g). Qed.
Lemma lem6993422 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term36 A B f s t) : term78 A B f t s.
Proof. exact (conj (@lem6993232 A B f s t h2) (@lem6993233 A s h1)). Qed.
Lemma lem6993423 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @IN B x t) (h3 : term36 A B f s t) : term79 A B x f t s.
Proof. exact (conj (@lem6993407 B x t h2) (@lem6993422 A B f s t h1 h3)). Qed.
Lemma lem6993424 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term75 A B x f s) (h3 : @IN B x t) (h4 : term36 A B f s t) : term80 A B x f t s.
Proof. exact (conj (@lem6993406 A B x f s h2) (@lem6993423 A B x f s t h1 h3 h4)). Qed.
Lemma lem6993434 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term81 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem6993435 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term81 B s t).
Proof. exact (@lem6993434 B s t). Qed.
Lemma lem6993436 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term36 A B f s t) = (term82 A B f s t).
Proof. exact (@lem6993435 B (@IMAGE A B f s) t). Qed.
Lemma lem6993443 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6993444 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term55 A B f s t) = (term83 A B f s t).
Proof. exact (MK_COMB (@lem6993443) (@lem6993436 A B f s t)). Qed.
Lemma lem6993445 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem6993446 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term78 A B f t s) = (term84 A B f t s).
Proof. exact (MK_COMB (@lem6993444 A B f s t) (@lem6993445 A s)). Qed.
Lemma lem6993449 {B : Type'} (x : B) (t : B -> Prop) : (term85 B x t) = (term85 B x t).
Proof. exact (eq_refl (term85 B x t)). Qed.
Lemma lem6993450 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term79 A B x f t s) = (term86 A B x f t s).
Proof. exact (MK_COMB (@lem6993449 B x t) (@lem6993446 A B f t s)). Qed.
Lemma lem6993453 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term87 A B x f s) = (term87 A B x f s).
Proof. exact (eq_refl (term87 A B x f s)). Qed.
Lemma lem6993454 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term80 A B x f t s) = (term88 A B x f t s).
Proof. exact (MK_COMB (@lem6993453 A B x f s) (@lem6993450 A B x f t s)). Qed.
Lemma lem6993457 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6993458 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term89 A B x f t s) = (term90 A B x f t s).
Proof. exact (MK_COMB (@lem6993457) (@lem6993454 A B x f t s)). Qed.
Lemma lem6993479 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term91 A B s f x g) = (term91 A B s f x g).
Proof. exact (eq_refl (term91 A B s f x g)). Qed.
Lemma lem6993480 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term92 A B t s f x g) = (term93 A B t s f x g).
Proof. exact (MK_COMB (@lem6993458 A B x f t s) (@lem6993479 A B s f x g)). Qed.
Lemma lem6993483 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term93 A B t s f x g) = (term92 A B t s f x g).
Proof. exact (SYM (@lem6993480 A B t s f x g)). Qed.
Lemma lem6993489 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term94 A B y f s) = (term95 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem6993490 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term94 A B y f s) = (term95 A B y f s).
Proof. exact (@lem6993489 A B y f s). Qed.
Lemma lem6993491 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term94 A B x f s) = (term95 A B x f s).
Proof. exact (@lem6993490 A B x f s). Qed.
Lemma lem6993501 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6993502 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6993501 A P x). Qed.
Lemma lem6993503 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem6993502 A s x). Qed.
Lemma lem6993504 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term96 A B x f x') = (term96 A B x f x').
Proof. exact (eq_refl (term96 A B x f x')). Qed.
Lemma lem6993505 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term97 A B x f x' s) = (term98 A B x f s x').
Proof. exact (MK_COMB (@lem6993504 A B x f x') (@lem6993503 A s x')). Qed.
Lemma lem6993508 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term99 A B x f s) = (term100 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem6993505 A B x f s x')). Qed.
Lemma lem6993509 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6993510 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term95 A B x f s) = (term101 A B x f s).
Proof. exact (MK_COMB (@lem6993509 A) (@lem6993508 A B x f s)). Qed.
Lemma lem6993515 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term94 A B x f s) = (term101 A B x f s).
Proof. exact (TRANS (@lem6993491 A B x f s) (@lem6993510 A B x f s)). Qed.
Lemma lem6993516 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6993517 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term75 A B x f s) = (term102 A B x f s).
Proof. exact (MK_COMB (@lem6993516) (@lem6993515 A B x f s)). Qed.
Lemma lem6993518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6993519 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term87 A B x f s) = (term103 A B x f s).
Proof. exact (MK_COMB (@lem6993518) (@lem6993517 A B x f s)). Qed.
Lemma lem6993523 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6993524 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem6993523 B P x). Qed.
Lemma lem6993525 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem6993524 B t x). Qed.
Lemma lem6993526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6993527 {B : Type'} (t : B -> Prop) (x : B) : (term85 B x t) = (term104 B t x).
Proof. exact (MK_COMB (@lem6993526) (@lem6993525 B t x)). Qed.
Lemma lem6993537 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term94 A B y f s) = (term95 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem6993538 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term94 A B y f s) = (term95 A B y f s).
Proof. exact (@lem6993537 A B y f s). Qed.
Lemma lem6993539 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term94 A B x f s) = (term95 A B x f s).
Proof. exact (@lem6993538 A B x f s). Qed.
Lemma lem6993549 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6993550 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6993549 A P x). Qed.
Lemma lem6993551 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem6993550 A s x). Qed.
Lemma lem6993552 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term96 A B x f x') = (term96 A B x f x').
Proof. exact (eq_refl (term96 A B x f x')). Qed.
Lemma lem6993553 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term97 A B x f x' s) = (term98 A B x f s x').
Proof. exact (MK_COMB (@lem6993552 A B x f x') (@lem6993551 A s x')). Qed.
Lemma lem6993556 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term99 A B x f s) = (term100 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem6993553 A B x f s x')). Qed.
Lemma lem6993557 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6993558 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term95 A B x f s) = (term101 A B x f s).
Proof. exact (MK_COMB (@lem6993557 A) (@lem6993556 A B x f s)). Qed.
Lemma lem6993563 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term94 A B x f s) = (term101 A B x f s).
Proof. exact (TRANS (@lem6993539 A B x f s) (@lem6993558 A B x f s)). Qed.
Lemma lem6993564 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6993565 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term105 A B x f s) = (term106 A B x f s).
Proof. exact (MK_COMB (@lem6993564) (@lem6993563 A B x f s)). Qed.
Lemma lem6993567 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6993568 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem6993567 B P x). Qed.
Lemma lem6993569 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem6993568 B t x). Qed.
Lemma lem6993570 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term107 A B f s x t) = (term108 A B f s t x).
Proof. exact (MK_COMB (@lem6993565 A B x f s) (@lem6993569 B t x)). Qed.
Lemma lem6993573 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term109 A B f s t) = (term110 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem6993570 A B f s t x)). Qed.
Lemma lem6993574 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6993575 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term82 A B f s t) = (term111 A B f s t).
Proof. exact (MK_COMB (@lem6993574 B) (@lem6993573 A B f s t)). Qed.
Lemma lem6993580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6993581 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term83 A B f s t) = (term112 A B f s t).
Proof. exact (MK_COMB (@lem6993580) (@lem6993575 A B f s t)). Qed.
Lemma lem6993582 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem6993583 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term84 A B f t s) = (term113 A B f t s).
Proof. exact (MK_COMB (@lem6993581 A B f s t) (@lem6993582 A s)). Qed.
Lemma lem6993586 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term86 A B x f t s) = (term114 A B x f t s).
Proof. exact (MK_COMB (@lem6993527 B t x) (@lem6993583 A B f t s)). Qed.
Lemma lem6993589 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term88 A B x f t s) = (term115 A B x f t s).
Proof. exact (MK_COMB (@lem6993519 A B x f s) (@lem6993586 A B x f t s)). Qed.
Lemma lem6993592 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6993593 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term90 A B x f t s) = (term116 A B x f t s).
Proof. exact (MK_COMB (@lem6993592) (@lem6993589 A B x f t s)). Qed.
Lemma lem6993601 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term117 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem6993602 {A : Type'} (p : A -> Prop) (x : A) : (term117 A x p) = (p x).
Proof. exact (@lem6993601 A p x). Qed.
Lemma lem6993603 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (x' : A) : (term118 A B x' s f x) = (term119 A B s f x x').
Proof. exact (@lem6993602 A (term120 A B s f x) x'). Qed.
Lemma lem6993604 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term119 A B s f x' x) = (term121 A B s f x x').
Proof. exact (eq_refl (term119 A B s f x' x)). Qed.
Lemma lem6993605 {A : Type'} (GEN_PVAR_296 : A) : (@SETSPEC A GEN_PVAR_296) = (@SETSPEC A GEN_PVAR_296).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_296)). Qed.
Lemma lem6993606 {A B : Type'} (GEN_PVAR_296 : A) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term122 A B GEN_PVAR_296 s f x' x) = (term123 A B GEN_PVAR_296 s f x x').
Proof. exact (MK_COMB (@lem6993605 A GEN_PVAR_296) (@lem6993604 A B s f x x')). Qed.
Lemma lem6993607 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6993608 {A B : Type'} (GEN_PVAR_296 : A) (s : A -> Prop) (f : A -> B) (x : B) (x' : A) : (term124 A B GEN_PVAR_296 s f x x') = (term125 A B GEN_PVAR_296 s f x x').
Proof. exact (MK_COMB (@lem6993606 A B GEN_PVAR_296 s f x' x) (@lem6993607 A x')). Qed.
Lemma lem6993609 {A B : Type'} (GEN_PVAR_296 : A) (s : A -> Prop) (f : A -> B) (x : B) : (term126 A B GEN_PVAR_296 s f x) = (term127 A B GEN_PVAR_296 s f x).
Proof. exact (fun_ext (fun x' : A => @lem6993608 A B GEN_PVAR_296 s f x x')). Qed.
Lemma lem6993610 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6993611 {A B : Type'} (GEN_PVAR_296 : A) (s : A -> Prop) (f : A -> B) (x : B) : (term128 A B GEN_PVAR_296 s f x) = (term129 A B GEN_PVAR_296 s f x).
Proof. exact (MK_COMB (@lem6993610 A) (@lem6993609 A B GEN_PVAR_296 s f x)). Qed.
Lemma lem6993612 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term130 A B s f x) = (term131 A B s f x).
Proof. exact (fun_ext (fun GEN_PVAR_296 : A => @lem6993611 A B GEN_PVAR_296 s f x)). Qed.
Lemma lem6993613 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6993614 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term132 A B s f x) = (term77 A B s f x).
Proof. exact (MK_COMB (@lem6993613 A) (@lem6993612 A B s f x)). Qed.
Lemma lem6993615 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6993616 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : B) : (term118 A B x s f x') = (term133 A B x s f x').
Proof. exact (MK_COMB (@lem6993615 A x) (@lem6993614 A B s f x')). Qed.
Lemma lem6993617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6993618 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : B) : (term134 A B x s f x') = (term135 A B x s f x').
Proof. exact (MK_COMB (@lem6993617) (@lem6993616 A B x s f x')). Qed.
Lemma lem6993619 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term119 A B s f x' x) = (term121 A B s f x x').
Proof. exact (eq_refl (term119 A B s f x' x)). Qed.
Lemma lem6993620 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : ((term118 A B x s f x') = (term119 A B s f x' x)) = ((term133 A B x s f x') = (term121 A B s f x x')).
Proof. exact (MK_COMB (@lem6993618 A B x s f x') (@lem6993619 A B s f x x')). Qed.
Lemma lem6993621 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term133 A B x s f x') = (term121 A B s f x x').
Proof. exact (EQ_MP (@lem6993620 A B s f x x') (@lem6993603 A B s f x' x)). Qed.
Lemma lem6993625 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6993626 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6993625 A P x). Qed.
Lemma lem6993627 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem6993626 A s x). Qed.
Lemma lem6993628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6993629 {A : Type'} (s : A -> Prop) (x : A) : (term85 A x s) = (term104 A s x).
Proof. exact (MK_COMB (@lem6993628) (@lem6993627 A s x)). Qed.
Lemma lem6993632 {A B : Type'} (f : A -> B) (x : A) (x' : B) : ((f x) = x') = ((f x) = x').
Proof. exact (eq_refl ((f x) = x')). Qed.
Lemma lem6993633 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term121 A B s f x x') = (term136 A B s f x x').
Proof. exact (MK_COMB (@lem6993629 A s x) (@lem6993632 A B f x x')). Qed.
Lemma lem6993636 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term133 A B x s f x') = (term136 A B s f x x').
Proof. exact (TRANS (@lem6993621 A B s f x x') (@lem6993633 A B s f x x')). Qed.
Lemma lem6993637 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6993638 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term137 A B x s f x') = (term138 A B s f x x').
Proof. exact (MK_COMB (@lem6993637) (@lem6993636 A B s f x x')). Qed.
Lemma lem6993641 {A : Type'} (g : A -> nat) (x : A) : ((g x) = (NUMERAL 0)) = ((g x) = (NUMERAL 0)).
Proof. exact (eq_refl ((g x) = (NUMERAL 0))). Qed.
Lemma lem6993642 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) (x' : A) : (term139 A B s f x g x') = (term140 A B s f x g x').
Proof. exact (MK_COMB (@lem6993638 A B s f x' x) (@lem6993641 A g x')). Qed.
Lemma lem6993645 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term141 A B s f x g) = (term142 A B s f x g).
Proof. exact (fun_ext (fun x' : A => @lem6993642 A B s f x g x')). Qed.
Lemma lem6993646 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6993647 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term91 A B s f x g) = (term143 A B s f x g).
Proof. exact (MK_COMB (@lem6993646 A) (@lem6993645 A B s f x g)). Qed.
Lemma lem6993652 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term93 A B t s f x g) = (term144 A B t s f x g).
Proof. exact (MK_COMB (@lem6993593 A B x f t s) (@lem6993647 A B s f x g)). Qed.
Lemma lem6993655 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term144 A B t s f x g) = (term93 A B t s f x g).
Proof. exact (SYM (@lem6993652 A B t s f x g)). Qed.
Lemma lem6993657 (p : Prop) : p = (term145 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6993658 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term144 A B t s f x g) = (term146 A B t s f x g).
Proof. exact (@lem6993657 (term144 A B t s f x g)). Qed.
Lemma lem6993659 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term146 A B t s f x g) = (term144 A B t s f x g).
Proof. exact (SYM (@lem6993658 A B t s f x g)). Qed.
Lemma lem6993660 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) (h1 : term147 A B t s f x g) : term147 A B t s f x g.
Proof. exact (h1). Qed.
Lemma lem6993663 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) (h1 : term146 A B t s f x g) : term146 A B t s f x g.
Proof. exact (h1). Qed.
Lemma lem6993664 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : term148 A B t s f x g.
Proof. exact (fun h0 : term146 A B t s f x g => @lem6993663 A B t s f x g h0). Qed.
Lemma lem6993665 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) (h1 : term148 A B t s f x g) : term148 A B t s f x g.
Proof. exact (h1). Qed.
Lemma lem6993666 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) (h1 : term146 A B t s f x g) : term146 A B t s f x g.
Proof. exact (h1). Qed.
Lemma lem6993667 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) (h1 : term146 A B t s f x g) (h2 : term148 A B t s f x g) : term146 A B t s f x g.
Proof. exact (@lem6993665 A B t s f x g h2 (@lem6993666 A B t s f x g h1)). Qed.
Lemma lem6993668 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) (h1 : term146 A B t s f x g) : term149 A B t s f x g.
Proof. exact (fun h0 : term148 A B t s f x g => @lem6993667 A B t s f x g h1 h0). Qed.
Lemma lem6993669 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) (h1 : term148 A B t s f x g) : term148 A B t s f x g.
Proof. exact (h1). Qed.
Lemma lem6993670 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) (h1 : term146 A B t s f x g) (h2 : term148 A B t s f x g) : term146 A B t s f x g.
Proof. exact (@lem6993668 A B t s f x g h1 (@lem6993669 A B t s f x g h2)). Qed.
Lemma lem6993671 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) (h1 : term148 A B t s f x g) : term148 A B t s f x g.
Proof. exact (fun h0 : term146 A B t s f x g => @lem6993670 A B t s f x g h0 h1). Qed.
Lemma lem6993672 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : term150 A B t s f x g.
Proof. exact (fun h0 : term148 A B t s f x g => @lem6993671 A B t s f x g h0). Qed.
Lemma lem6993675 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : term148 A B t s f x g.
Proof. exact (@lem6993672 A B t s f x g (@lem6993664 A B t s f x g)). Qed.
Lemma lem6993676 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : term148 A B t s f x g.
Proof. exact (@lem6993675 A B t s f x g). Qed.
Lemma lem6993698 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6993699 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term146 A B t s f x g) = (term151 A B t s f x g).
Proof. exact (@lem6993698 (term147 A B t s f x g)). Qed.
Lemma lem6993701 (t : Prop) : (term152 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6993702 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term151 A B t s f x g) = (term144 A B t s f x g).
Proof. exact (@lem6993701 (term144 A B t s f x g)). Qed.
Lemma lem6993705 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term146 A B t s f x g) = (term144 A B t s f x g).
Proof. exact (TRANS (@lem6993699 A B t s f x g) (@lem6993702 A B t s f x g)). Qed.
Lemma lem6993794 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term153 A B s f x g) = (term154 A B s f x g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6993705 A B t s f x g)). Qed.
Lemma lem6993795 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6993796 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term155 A B s f x g) = (term156 A B s f x g).
Proof. exact (MK_COMB (@lem6993795 B) (@lem6993794 A B s f x g)). Qed.
Lemma lem6993801 {A B : Type'} (f : A -> B) (x : B) (g : A -> nat) : (term157 A B f x g) = (term158 A B f x g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6993796 A B s f x g)). Qed.
Lemma lem6993802 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6993803 {A B : Type'} (f : A -> B) (x : B) (g : A -> nat) : (term159 A B f x g) = (term160 A B f x g).
Proof. exact (MK_COMB (@lem6993802 A) (@lem6993801 A B f x g)). Qed.
Lemma lem6993808 {A B : Type'} (x : B) (g : A -> nat) : (term161 A B x g) = (term162 A B x g).
Proof. exact (fun_ext (fun f : A -> B => @lem6993803 A B f x g)). Qed.
Lemma lem6993809 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6993810 {A B : Type'} (x : B) (g : A -> nat) : (term163 A B x g) = (term164 A B x g).
Proof. exact (MK_COMB (@lem6993809 A B) (@lem6993808 A B x g)). Qed.
Lemma lem6993815 {A B : Type'} (g : A -> nat) : (term165 A B g) = (term166 A B g).
Proof. exact (fun_ext (fun x : B => @lem6993810 A B x g)). Qed.
Lemma lem6993816 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6993817 {A B : Type'} (g : A -> nat) : (term167 A B g) = (term168 A B g).
Proof. exact (MK_COMB (@lem6993816 B) (@lem6993815 A B g)). Qed.
Lemma lem6993822 {A B : Type'} : (term169 A B) = (term170 A B).
Proof. exact (fun_ext (fun g : A -> nat => @lem6993817 A B g)). Qed.
Lemma lem6993823 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6993832 {A B : Type'} : (term171 A B) = (term172 A B).
Proof. exact (MK_COMB (@lem6993823 A) (@lem6993822 A B)). Qed.
Lemma lem6993841 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) (x' : A) : (term140 A B s f x g x') = (term140 A B s f x g x').
Proof. exact (eq_refl (term140 A B s f x g x')). Qed.
Lemma lem6993842 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term142 A B s f x g) = (term142 A B s f x g).
Proof. exact (fun_ext (fun x' : A => @lem6993841 A B s f x g x')). Qed.
Lemma lem6993843 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6993844 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term143 A B s f x g) = (term143 A B s f x g).
Proof. exact (MK_COMB (@lem6993843 A) (@lem6993842 A B s f x g)). Qed.
Lemma lem6993845 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem6993846 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem6993851 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term98 A B x f s x') = (term98 A B x f s x').
Proof. exact (eq_refl (term98 A B x f s x')). Qed.
Lemma lem6993852 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term100 A B x f s) = (term100 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem6993851 A B x f s x')). Qed.
Lemma lem6993853 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6993854 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term101 A B x f s) = (term101 A B x f s).
Proof. exact (MK_COMB (@lem6993853 A) (@lem6993852 A B x f s)). Qed.
Lemma lem6993855 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6993856 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term106 A B x f s) = (term106 A B x f s).
Proof. exact (MK_COMB (@lem6993855) (@lem6993854 A B x f s)). Qed.
Lemma lem6993857 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term108 A B f s t x) = (term108 A B f s t x).
Proof. exact (MK_COMB (@lem6993856 A B x f s) (@lem6993846 B t x)). Qed.
Lemma lem6993858 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term110 A B f s t) = (term110 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem6993857 A B f s t x)). Qed.
Lemma lem6993859 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6993860 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term111 A B f s t) = (term111 A B f s t).
Proof. exact (MK_COMB (@lem6993859 B) (@lem6993858 A B f s t)). Qed.
Lemma lem6993861 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6993862 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term112 A B f s t) = (term112 A B f s t).
Proof. exact (MK_COMB (@lem6993861) (@lem6993860 A B f s t)). Qed.
Lemma lem6993863 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term113 A B f t s) = (term113 A B f t s).
Proof. exact (MK_COMB (@lem6993862 A B f s t) (@lem6993845 A s)). Qed.
Lemma lem6993866 {B : Type'} (t : B -> Prop) (x : B) : (term104 B t x) = (term104 B t x).
Proof. exact (eq_refl (term104 B t x)). Qed.
Lemma lem6993867 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term114 A B x f t s) = (term114 A B x f t s).
Proof. exact (MK_COMB (@lem6993866 B t x) (@lem6993863 A B f t s)). Qed.
Lemma lem6993872 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term98 A B x f s x') = (term98 A B x f s x').
Proof. exact (eq_refl (term98 A B x f s x')). Qed.
Lemma lem6993873 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term100 A B x f s) = (term100 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem6993872 A B x f s x')). Qed.
Lemma lem6993874 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6993875 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term101 A B x f s) = (term101 A B x f s).
Proof. exact (MK_COMB (@lem6993874 A) (@lem6993873 A B x f s)). Qed.
Lemma lem6993876 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6993877 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term102 A B x f s) = (term102 A B x f s).
Proof. exact (MK_COMB (@lem6993876) (@lem6993875 A B x f s)). Qed.
Lemma lem6993878 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6993879 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term103 A B x f s) = (term103 A B x f s).
Proof. exact (MK_COMB (@lem6993878) (@lem6993877 A B x f s)). Qed.
Lemma lem6993880 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term115 A B x f t s) = (term115 A B x f t s).
Proof. exact (MK_COMB (@lem6993879 A B x f s) (@lem6993867 A B x f t s)). Qed.
Lemma lem6993881 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6993882 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term116 A B x f t s) = (term116 A B x f t s).
Proof. exact (MK_COMB (@lem6993881) (@lem6993880 A B x f t s)). Qed.
Lemma lem6993883 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term144 A B t s f x g) = (term144 A B t s f x g).
Proof. exact (MK_COMB (@lem6993882 A B x f t s) (@lem6993844 A B s f x g)). Qed.
Lemma lem6993884 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term154 A B s f x g) = (term154 A B s f x g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6993883 A B t s f x g)). Qed.
Lemma lem6993885 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6993886 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term156 A B s f x g) = (term156 A B s f x g).
Proof. exact (MK_COMB (@lem6993885 B) (@lem6993884 A B s f x g)). Qed.
Lemma lem6993887 {A B : Type'} (f : A -> B) (x : B) (g : A -> nat) : (term158 A B f x g) = (term158 A B f x g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6993886 A B s f x g)). Qed.
Lemma lem6993888 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6993889 {A B : Type'} (f : A -> B) (x : B) (g : A -> nat) : (term160 A B f x g) = (term160 A B f x g).
Proof. exact (MK_COMB (@lem6993888 A) (@lem6993887 A B f x g)). Qed.
Lemma lem6993890 {A B : Type'} (x : B) (g : A -> nat) : (term162 A B x g) = (term162 A B x g).
Proof. exact (fun_ext (fun f : A -> B => @lem6993889 A B f x g)). Qed.
Lemma lem6993891 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6993892 {A B : Type'} (x : B) (g : A -> nat) : (term164 A B x g) = (term164 A B x g).
Proof. exact (MK_COMB (@lem6993891 A B) (@lem6993890 A B x g)). Qed.
Lemma lem6993893 {A B : Type'} (g : A -> nat) : (term166 A B g) = (term166 A B g).
Proof. exact (fun_ext (fun x : B => @lem6993892 A B x g)). Qed.
Lemma lem6993894 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6993895 {A B : Type'} (g : A -> nat) : (term168 A B g) = (term168 A B g).
Proof. exact (MK_COMB (@lem6993894 B) (@lem6993893 A B g)). Qed.
Lemma lem6993896 {A B : Type'} : (term170 A B) = (term170 A B).
Proof. exact (fun_ext (fun g : A -> nat => @lem6993895 A B g)). Qed.
Lemma lem6993897 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6993898 {A B : Type'} : (term172 A B) = (term172 A B).
Proof. exact (MK_COMB (@lem6993897 A) (@lem6993896 A B)). Qed.
Lemma lem6993973 {A B : Type'} : (term171 A B) = (term172 A B).
Proof. exact (TRANS (@lem6993832 A B) (@lem6993898 A B)). Qed.
Lemma lem6993974 {A B : Type'} : (term172 A B) = (term171 A B).
Proof. exact (SYM (@lem6993973 A B)). Qed.
Lemma lem6993975 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term115 A B x f t s) : term115 A B x f t s.
Proof. exact (h1). Qed.
Lemma lem6993978 (p : Prop) : p = (term145 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6993979 {A : Type'} (g : A -> nat) (x' : A) : ((g x') = (NUMERAL 0)) = (term173 A g x').
Proof. exact (@lem6993978 ((g x') = (NUMERAL 0))). Qed.
Lemma lem6993980 {A : Type'} (g : A -> nat) (x' : A) : (term173 A g x') = ((g x') = (NUMERAL 0)).
Proof. exact (SYM (@lem6993979 A g x')). Qed.
Lemma lem6993988 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term174 A B x f s x') = (term175 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem6993989 {A : Type'} (P : A -> Prop) : (term176 A P) = (term177 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem6993990 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term102 A B x f s) = (term178 A B x f s).
Proof. exact (@lem6993989 A (term100 A B x f s)). Qed.
Lemma lem6993991 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term179 A B x f s x') = (term98 A B x f s x').
Proof. exact (eq_refl (term179 A B x f s x')). Qed.
Lemma lem6993992 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6993993 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term180 A B x f s x') = (term174 A B x f s x').
Proof. exact (MK_COMB (@lem6993992) (@lem6993991 A B x f s x')). Qed.
Lemma lem6993994 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term180 A B x f s x') = (term175 A B x f s x').
Proof. exact (TRANS (@lem6993993 A B x f s x') (@lem6993988 A B x f s x')). Qed.
Lemma lem6993995 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term181 A B x f s) = (term182 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem6993994 A B x f s x')). Qed.
Lemma lem6993996 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6993997 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term178 A B x f s) = (term183 A B x f s).
Proof. exact (MK_COMB (@lem6993996 A) (@lem6993995 A B x f s)). Qed.
Lemma lem6993998 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term102 A B x f s) = (term183 A B x f s).
Proof. exact (TRANS (@lem6993990 A B x f s) (@lem6993997 A B x f s)). Qed.
Lemma lem6994006 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term174 A B x f s x') = (term175 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem6994007 {A : Type'} (P : A -> Prop) : (term176 A P) = (term177 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem6994008 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term102 A B x f s) = (term178 A B x f s).
Proof. exact (@lem6994007 A (term100 A B x f s)). Qed.
Lemma lem6994009 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term179 A B x f s x') = (term98 A B x f s x').
Proof. exact (eq_refl (term179 A B x f s x')). Qed.
Lemma lem6994010 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6994011 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term180 A B x f s x') = (term174 A B x f s x').
Proof. exact (MK_COMB (@lem6994010) (@lem6994009 A B x f s x')). Qed.
Lemma lem6994012 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term180 A B x f s x') = (term175 A B x f s x').
Proof. exact (TRANS (@lem6994011 A B x f s x') (@lem6994006 A B x f s x')). Qed.
Lemma lem6994013 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term181 A B x f s) = (term182 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem6994012 A B x f s x')). Qed.
Lemma lem6994014 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6994015 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term178 A B x f s) = (term183 A B x f s).
Proof. exact (MK_COMB (@lem6994014 A) (@lem6994013 A B x f s)). Qed.
Lemma lem6994016 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term102 A B x f s) = (term183 A B x f s).
Proof. exact (TRANS (@lem6994008 A B x f s) (@lem6994015 A B x f s)). Qed.
Lemma lem6994017 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem6994018 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6994019 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term184 A B x f s) = (term185 A B x f s).
Proof. exact (MK_COMB (@lem6994018) (@lem6994016 A B x f s)). Qed.
Lemma lem6994020 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term186 A B f s t x) = (term187 A B f s t x).
Proof. exact (MK_COMB (@lem6994019 A B x f s) (@lem6994017 B t x)). Qed.
Lemma lem6994021 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term108 A B f s t x) = (term186 A B f s t x).
Proof. exact (@lem17265 (term101 A B x f s) (t x)). Qed.
Lemma lem6994022 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term108 A B f s t x) = (term187 A B f s t x).
Proof. exact (TRANS (@lem6994021 A B f s t x) (@lem6994020 A B f s t x)). Qed.
Lemma lem6994023 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term110 A B f s t) = (term188 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem6994022 A B f s t x)). Qed.
Lemma lem6994024 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6994025 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term111 A B f s t) = (term189 A B f s t).
Proof. exact (MK_COMB (@lem6994024 B) (@lem6994023 A B f s t)). Qed.
Lemma lem6994026 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem6994027 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6994028 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term112 A B f s t) = (term190 A B f s t).
Proof. exact (MK_COMB (@lem6994027) (@lem6994025 A B f s t)). Qed.
Lemma lem6994029 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term113 A B f t s) = (term191 A B f t s).
Proof. exact (MK_COMB (@lem6994028 A B f s t) (@lem6994026 A s)). Qed.
Lemma lem6994031 {B : Type'} (t : B -> Prop) (x : B) : (term104 B t x) = (term104 B t x).
Proof. exact (eq_refl (term104 B t x)). Qed.
Lemma lem6994032 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term114 A B x f t s) = (term192 A B x f t s).
Proof. exact (MK_COMB (@lem6994031 B t x) (@lem6994029 A B f t s)). Qed.
Lemma lem6994033 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6994034 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term103 A B x f s) = (term193 A B x f s).
Proof. exact (MK_COMB (@lem6994033) (@lem6993998 A B x f s)). Qed.
Lemma lem6994167 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term115 A B x f t s) = (term194 A B x f t s).
Proof. exact (MK_COMB (@lem6994034 A B x f s) (@lem6994032 A B x f t s)). Qed.
Lemma lem6994168 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term115 A B x f t s) : term194 A B x f t s.
Proof. exact (EQ_MP (@lem6994167 A B x f t s) (@lem6993975 A B x f t s h1)). Qed.
Lemma lem6994178 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term136 A B s f x' x) : term136 A B s f x' x.
Proof. exact (h1). Qed.
Lemma lem6994187 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem6994190 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem6994191 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6994196 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6994197 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem6994196 A Prop f x). Qed.
Lemma lem6994199 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem6994197 A s x). Qed.
Lemma lem6994200 {A : Type'} (s : A -> Prop) (x : A) : (term195 A s x) = (term196 A s x).
Proof. exact (MK_COMB (@lem6994191) (@lem6994199 A s x)). Qed.
Lemma lem6994211 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term197 A B x f x') = (term197 A B x f x').
Proof. exact (eq_refl (term197 A B x f x')). Qed.
Lemma lem6994212 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term175 A B x f s x') = (term198 A B x f s x').
Proof. exact (MK_COMB (@lem6994211 A B x f x') (@lem6994200 A s x')). Qed.
Lemma lem6994213 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term182 A B x f s) = (term199 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem6994212 A B x f s x')). Qed.
Lemma lem6994214 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6994215 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term183 A B x f s) = (term200 A B x f s).
Proof. exact (MK_COMB (@lem6994214 A) (@lem6994213 A B x f s)). Qed.
Lemma lem6994216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6994217 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term185 A B x f s) = (term201 A B x f s).
Proof. exact (MK_COMB (@lem6994216) (@lem6994215 A B x f s)). Qed.
Lemma lem6994218 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term187 A B f s t x) = (term202 A B f s t x).
Proof. exact (MK_COMB (@lem6994217 A B x f s) (@lem6994190 B t x)). Qed.
Lemma lem6994219 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term188 A B f s t) = (term203 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem6994218 A B f s t x)). Qed.
Lemma lem6994220 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6994221 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term189 A B f s t) = (term204 A B f s t).
Proof. exact (MK_COMB (@lem6994220 B) (@lem6994219 A B f s t)). Qed.
Lemma lem6994222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6994223 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term190 A B f s t) = (term205 A B f s t).
Proof. exact (MK_COMB (@lem6994222) (@lem6994221 A B f s t)). Qed.
Lemma lem6994224 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term191 A B f t s) = (term206 A B f t s).
Proof. exact (MK_COMB (@lem6994223 A B f s t) (@lem6994187 A s)). Qed.
Lemma lem6994229 {B : Type'} (t : B -> Prop) (x : B) : (term104 B t x) = (term104 B t x).
Proof. exact (eq_refl (term104 B t x)). Qed.
Lemma lem6994230 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term192 A B x f t s) = (term207 A B x f t s).
Proof. exact (MK_COMB (@lem6994229 B t x) (@lem6994224 A B f t s)). Qed.
Lemma lem6994231 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6994236 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6994237 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem6994236 A Prop f x). Qed.
Lemma lem6994239 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem6994237 A s x). Qed.
Lemma lem6994240 {A : Type'} (s : A -> Prop) (x : A) : (term195 A s x) = (term196 A s x).
Proof. exact (MK_COMB (@lem6994231) (@lem6994239 A s x)). Qed.
Lemma lem6994251 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term197 A B x f x') = (term197 A B x f x').
Proof. exact (eq_refl (term197 A B x f x')). Qed.
Lemma lem6994252 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term175 A B x f s x') = (term198 A B x f s x').
Proof. exact (MK_COMB (@lem6994251 A B x f x') (@lem6994240 A s x')). Qed.
Lemma lem6994253 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term182 A B x f s) = (term199 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem6994252 A B x f s x')). Qed.
Lemma lem6994254 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6994255 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term183 A B x f s) = (term200 A B x f s).
Proof. exact (MK_COMB (@lem6994254 A) (@lem6994253 A B x f s)). Qed.
Lemma lem6994256 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6994257 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term193 A B x f s) = (term208 A B x f s).
Proof. exact (MK_COMB (@lem6994256) (@lem6994255 A B x f s)). Qed.
Lemma lem6994258 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term194 A B x f t s) = (term209 A B x f t s).
Proof. exact (MK_COMB (@lem6994257 A B x f s) (@lem6994230 A B x f t s)). Qed.
Lemma lem6994259 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term115 A B x f t s) : term209 A B x f t s.
Proof. exact (EQ_MP (@lem6994258 A B x f t s) (@lem6994168 A B x f t s h1)). Qed.
Lemma lem6994266 {A B : Type'} (f : A -> B) (x' : A) (x : B) : ((f x') = x) = ((f x') = x).
Proof. exact (eq_refl ((f x') = x)). Qed.
Lemma lem6994271 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6994272 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem6994271 A Prop f x). Qed.
Lemma lem6994274 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem6994272 A s x'). Qed.
Lemma lem6994275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6994276 {A : Type'} (s : A -> Prop) (x' : A) : (term104 A s x') = (term210 A s x').
Proof. exact (MK_COMB (@lem6994275) (@lem6994274 A s x')). Qed.
Lemma lem6994277 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) : (term136 A B s f x' x) = (term211 A B s f x' x).
Proof. exact (MK_COMB (@lem6994276 A s x') (@lem6994266 A B f x' x)). Qed.
Lemma lem6994278 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term136 A B s f x' x) : term211 A B s f x' x.
Proof. exact (EQ_MP (@lem6994277 A B s f x' x) (@lem6994178 A B s f x' x h1)). Qed.
Lemma lem6994294 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term115 A B x f t s) : term200 A B x f s.
Proof. exact (proj1 (@lem6994259 A B x f t s h1)). Qed.
Lemma lem6994318 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term198 A B x f s x') = (term198 A B x f s x').
Proof. exact (eq_refl (term198 A B x f s x')). Qed.
Lemma lem6994319 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term199 A B x f s) = (term199 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem6994318 A B x f s x')). Qed.
Lemma lem6994320 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6994322 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term200 A B x f s) = (term200 A B x f s).
Proof. exact (MK_COMB (@lem6994320 A) (@lem6994319 A B x f s)). Qed.
Lemma lem6994323 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term115 A B x f t s) : term200 A B x f s.
Proof. exact (EQ_MP (@lem6994322 A B x f s) (@lem6994294 A B x f t s h1)). Qed.
Lemma lem6994380 {A B : Type'} (_93227 : A) (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term115 A B x f t s) : term212 A B x f s _93227.
Proof. exact (@lem6994323 A B x f t s h1 _93227). Qed.
Lemma lem6994381 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_93227 : A) : (term212 A B x f s _93227) = (term198 A B x f s _93227).
Proof. exact (eq_refl (term212 A B x f s _93227)). Qed.
Lemma lem6994394 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term136 A B s f x' x) : (f x') = x.
Proof. exact (proj2 (@lem6994278 A B s f x' x h1)). Qed.
Lemma lem6994400 {A B : Type'} (_93227 : A) (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term115 A B x f t s) : term198 A B x f s _93227.
Proof. exact (EQ_MP (@lem6994381 A B x f s _93227) (@lem6994380 A B _93227 x f t s h1)). Qed.
Lemma lem6994417 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term136 A B s f x' x) : x = (f x').
Proof. exact (SYM (@lem6994394 A B s f x' x h1)). Qed.
Lemma lem6994460 {A B : Type'} (f : A -> B) (s : A -> Prop) (_93227 : A) : (term213 A B f s _93227) = (term213 A B f s _93227).
Proof. exact (eq_refl (term213 A B f s _93227)). Qed.
Lemma lem6994461 {A B : Type'} (_93227 : A) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term136 A B s f x' x) : (term214 A B f s _93227 x) = (term215 A B s _93227 f x').
Proof. exact (MK_COMB (@lem6994460 A B f s _93227) (@lem6994417 A B s f x' x h1)). Qed.
Lemma lem6994462 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_93227 : A) : (term215 A B s _93227 f x') = (term216 A B x' f s _93227).
Proof. exact (eq_refl (term215 A B s _93227 f x')). Qed.
Lemma lem6994463 {A B : Type'} (f : A -> B) (s : A -> Prop) (_93227 : A) (x : B) : (term217 A B f s _93227 x) = (term217 A B f s _93227 x).
Proof. exact (eq_refl (term217 A B f s _93227 x)). Qed.
Lemma lem6994464 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_93227 : A) : ((term214 A B f s _93227 x) = (term215 A B s _93227 f x')) = ((term214 A B f s _93227 x) = (term216 A B x' f s _93227)).
Proof. exact (MK_COMB (@lem6994463 A B f s _93227 x) (@lem6994462 A B x' f s _93227)). Qed.
Lemma lem6994465 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_93227 : A) : (term214 A B f s _93227 x) = (term198 A B x f s _93227).
Proof. exact (eq_refl (term214 A B f s _93227 x)). Qed.
Lemma lem6994466 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6994467 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_93227 : A) : (term217 A B f s _93227 x) = (term218 A B x f s _93227).
Proof. exact (MK_COMB (@lem6994466) (@lem6994465 A B x f s _93227)). Qed.
Lemma lem6994468 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_93227 : A) : (term216 A B x' f s _93227) = (term216 A B x' f s _93227).
Proof. exact (eq_refl (term216 A B x' f s _93227)). Qed.
Lemma lem6994469 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_93227 : A) : ((term214 A B f s _93227 x) = (term216 A B x' f s _93227)) = ((term198 A B x f s _93227) = (term216 A B x' f s _93227)).
Proof. exact (MK_COMB (@lem6994467 A B x f s _93227) (@lem6994468 A B x' f s _93227)). Qed.
Lemma lem6994470 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_93227 : A) : ((term214 A B f s _93227 x) = (term215 A B s _93227 f x')) = ((term198 A B x f s _93227) = (term216 A B x' f s _93227)).
Proof. exact (TRANS (@lem6994464 A B x x' f s _93227) (@lem6994469 A B x x' f s _93227)). Qed.
Lemma lem6994471 {A B : Type'} (_93227 : A) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term136 A B s f x' x) : (term198 A B x f s _93227) = (term216 A B x' f s _93227).
Proof. exact (EQ_MP (@lem6994470 A B x x' f s _93227) (@lem6994461 A B _93227 s f x' x h1)). Qed.
Lemma lem6994472 {A B : Type'} (_93227 : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term115 A B x f t s) (h2 : term136 A B s f x' x) : term216 A B x' f s _93227.
Proof. exact (EQ_MP (@lem6994471 A B _93227 s f x' x h2) (@lem6994400 A B _93227 x f t s h1)). Qed.
Lemma lem6994590 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem6994591 {B : Type'} (x : B) : x = x.
Proof. exact (@lem6994590 B x). Qed.
Lemma lem6994592 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem6994591 B (f x')). Qed.
Lemma lem6994593 {A B : Type'} (f : A -> B) (x' : A) : term219 A B f x'.
Proof. exact (fun h0 : term220 A B f x' => @lem6994592 A B f x'). Qed.
Lemma lem6994595 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6994596 {A B : Type'} (f : A -> B) (x' : A) : (term219 A B f x') = ((f x') = (f x')).
Proof. exact (@lem6994595 ((f x') = (f x'))). Qed.
Lemma lem6994597 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem6994596 A B f x') (@lem6994593 A B f x')). Qed.
Lemma lem6994599 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term136 A B s f x' x) : @I (A -> Prop) s x'.
Proof. exact (proj1 (@lem6994278 A B s f x' x h1)). Qed.
Lemma lem6994600 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term136 A B s f x' x) : term222 A s x'.
Proof. exact (fun h0 : term196 A s x' => @lem6994599 A B s f x' x h1). Qed.
Lemma lem6994602 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6994603 {A : Type'} (s : A -> Prop) (x' : A) : (term222 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem6994602 (@I (A -> Prop) s x')). Qed.
Lemma lem6994604 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term136 A B s f x' x) : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem6994603 A s x') (@lem6994600 A B s f x' x h1)). Qed.
Lemma lem6994606 (a : Prop) (b : Prop) : (term223 a b) = (term224 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem6994607 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_93227 : A) : (term216 A B x' f s _93227) = (term225 A B x' f s _93227).
Proof. exact (@lem6994606 ((f x') = (f _93227)) (@I (A -> Prop) s _93227)). Qed.
Lemma lem6994609 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6994610 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_93227 : A) : (term225 A B x' f s _93227) = (term226 A B x' f s _93227).
Proof. exact (@lem6994609 (term227 A B x' f s _93227)). Qed.
Lemma lem6994611 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_93227 : A) : (term216 A B x' f s _93227) = (term226 A B x' f s _93227).
Proof. exact (TRANS (@lem6994607 A B x' f s _93227) (@lem6994610 A B x' f s _93227)). Qed.
Lemma lem6994613 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term136 A B s f x' x) : term228 A B f s x'.
Proof. exact (conj (@lem6994597 A B f x') (@lem6994604 A B s f x' x h1)). Qed.
Lemma lem6994615 {A B : Type'} (_93227 : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term115 A B x f t s) (h2 : term136 A B s f x' x) : term226 A B x' f s _93227.
Proof. exact (EQ_MP (@lem6994611 A B x' f s _93227) (@lem6994472 A B _93227 t s f x' x h1 h2)). Qed.
Lemma lem6994616 {A B : Type'} (_93227 : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term115 A B x f t s) (h2 : term136 A B s f x' x) : term226 A B x' f s _93227.
Proof. exact (@lem6994615 A B _93227 t s f x' x h1 h2). Qed.
Lemma lem6994617 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term115 A B x f t s) (h2 : term136 A B s f x' x) : term229 A B f s x'.
Proof. exact (@lem6994616 A B x' t s f x' x h1 h2). Qed.
Lemma lem6994620 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term115 A B x f t s) (h2 : term136 A B s f x' x) : False.
Proof. exact (@lem6994617 A B t s f x' x h1 h2 (@lem6994613 A B s f x' x h2)). Qed.
Lemma lem6994621 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term115 A B x f t s) (h2 : term136 A B s f x' x) : term230.
Proof. exact (fun h0 : ~ False => @lem6994620 A B t s f x' x h1 h2). Qed.
Lemma lem6994623 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6994624 : term230 = False.
Proof. exact (@lem6994623 False). Qed.
Lemma lem6994626 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term115 A B x f t s) (h2 : term136 A B s f x' x) : False.
Proof. exact (EQ_MP (@lem6994624) (@lem6994621 A B t s f x' x h1 h2)). Qed.
Lemma lem6994627 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term115 A B x f t s) (h2 : term136 A B s f x' x) : (term136 A B s f x' x) = False.
Proof. exact (prop_ext (fun h3 : term136 A B s f x' x => @lem6994626 A B t s f x' x h1 h2) (fun h3 : False => @lem6994178 A B s f x' x h2)). Qed.
Lemma lem6994628 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term115 A B x f t s) (h2 : term136 A B s f x' x) : False.
Proof. exact (EQ_MP (@lem6994627 A B t s f x' x h1 h2) (@lem6994178 A B s f x' x h2)). Qed.
Lemma lem6994629 {A B : Type'} (g : A -> nat) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term115 A B x f t s) (h2 : term136 A B s f x' x) : term173 A g x'.
Proof. exact (fun h0 : term231 A g x' => @lem6994628 A B t s f x' x h1 h2). Qed.
Lemma lem6994630 {A B : Type'} (g : A -> nat) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term115 A B x f t s) (h2 : term136 A B s f x' x) : (g x') = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6993980 A g x') (@lem6994629 A B g t s f x' x h1 h2)). Qed.
Lemma lem6994631 {A B : Type'} (g : A -> nat) (x' : A) (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term115 A B x f t s) : term140 A B s f x g x'.
Proof. exact (fun h0 : term136 A B s f x' x => @lem6994630 A B g t s f x' x h1 h0). Qed.
Lemma lem6994636 {A B : Type'} (g : A -> nat) (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term115 A B x f t s) : term143 A B s f x g.
Proof. exact (fun x' : A => @lem6994631 A B g x' x f t s h1). Qed.
Lemma lem6994637 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : term144 A B t s f x g.
Proof. exact (fun h0 : term115 A B x f t s => @lem6994636 A B g x f t s h0). Qed.
Lemma lem6994642 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : term156 A B s f x g.
Proof. exact (fun t : B -> Prop => @lem6994637 A B t s f x g). Qed.
Lemma lem6994647 {A B : Type'} (f : A -> B) (x : B) (g : A -> nat) : term160 A B f x g.
Proof. exact (fun s : A -> Prop => @lem6994642 A B s f x g). Qed.
Lemma lem6994652 {A B : Type'} (x : B) (g : A -> nat) : term164 A B x g.
Proof. exact (fun f : A -> B => @lem6994647 A B f x g). Qed.
Lemma lem6994657 {A B : Type'} (g : A -> nat) : term168 A B g.
Proof. exact (fun x : B => @lem6994652 A B x g). Qed.
Lemma lem6994662 {A B : Type'} : term172 A B.
Proof. exact (fun g : A -> nat => @lem6994657 A B g). Qed.
Lemma lem6994663 {A B : Type'} : term171 A B.
Proof. exact (EQ_MP (@lem6993974 A B) (@lem6994662 A B)). Qed.
Lemma lem6994664 {A B : Type'} (g : A -> nat) : term232 A B g.
Proof. exact (@lem6994663 A B g). Qed.
Lemma lem6994665 {A B : Type'} (g : A -> nat) : (term232 A B g) = (term167 A B g).
Proof. exact (eq_refl (term232 A B g)). Qed.
Lemma lem6994666 {A B : Type'} (g : A -> nat) : term167 A B g.
Proof. exact (EQ_MP (@lem6994665 A B g) (@lem6994664 A B g)). Qed.
Lemma lem6994667 {A B : Type'} (g : A -> nat) (x : B) : term233 A B g x.
Proof. exact (@lem6994666 A B g x). Qed.
Lemma lem6994668 {A B : Type'} (x : B) (g : A -> nat) : (term233 A B g x) = (term163 A B x g).
Proof. exact (eq_refl (term233 A B g x)). Qed.
Lemma lem6994669 {A B : Type'} (x : B) (g : A -> nat) : term163 A B x g.
Proof. exact (EQ_MP (@lem6994668 A B x g) (@lem6994667 A B g x)). Qed.
Lemma lem6994670 {A B : Type'} (x : B) (g : A -> nat) (f : A -> B) : term234 A B x g f.
Proof. exact (@lem6994669 A B x g f). Qed.
Lemma lem6994671 {A B : Type'} (f : A -> B) (x : B) (g : A -> nat) : (term234 A B x g f) = (term159 A B f x g).
Proof. exact (eq_refl (term234 A B x g f)). Qed.
Lemma lem6994672 {A B : Type'} (f : A -> B) (x : B) (g : A -> nat) : term159 A B f x g.
Proof. exact (EQ_MP (@lem6994671 A B f x g) (@lem6994670 A B x g f)). Qed.
Lemma lem6994673 {A B : Type'} (f : A -> B) (x : B) (g : A -> nat) (s : A -> Prop) : term235 A B f x g s.
Proof. exact (@lem6994672 A B f x g s). Qed.
Lemma lem6994674 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term235 A B f x g s) = (term155 A B s f x g).
Proof. exact (eq_refl (term235 A B f x g s)). Qed.
Lemma lem6994675 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : term155 A B s f x g.
Proof. exact (EQ_MP (@lem6994674 A B s f x g) (@lem6994673 A B f x g s)). Qed.
Lemma lem6994676 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) (t : B -> Prop) : term236 A B s f x g t.
Proof. exact (@lem6994675 A B s f x g t). Qed.
Lemma lem6994677 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : (term236 A B s f x g t) = (term146 A B t s f x g).
Proof. exact (eq_refl (term236 A B s f x g t)). Qed.
Lemma lem6994678 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : term146 A B t s f x g.
Proof. exact (EQ_MP (@lem6994677 A B t s f x g) (@lem6994676 A B s f x g t)). Qed.
Lemma lem6994680 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : term146 A B t s f x g.
Proof. exact (@lem6993676 A B t s f x g (@lem6994678 A B t s f x g)). Qed.
Lemma lem6994681 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) (h1 : term147 A B t s f x g) : False.
Proof. exact (@lem6994680 A B t s f x g (@lem6993660 A B t s f x g h1)). Qed.
Lemma lem6994682 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) (h1 : term147 A B t s f x g) : (term147 A B t s f x g) = False.
Proof. exact (prop_ext (fun h2 : term147 A B t s f x g => @lem6994681 A B t s f x g h1) (fun h2 : False => @lem6993660 A B t s f x g h1)). Qed.
Lemma lem6994683 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) (h1 : term147 A B t s f x g) : False.
Proof. exact (EQ_MP (@lem6994682 A B t s f x g h1) (@lem6993660 A B t s f x g h1)). Qed.
Lemma lem6994684 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : term146 A B t s f x g.
Proof. exact (fun h0 : term147 A B t s f x g => @lem6994683 A B t s f x g h0). Qed.
Lemma lem6994685 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : term144 A B t s f x g.
Proof. exact (EQ_MP (@lem6993659 A B t s f x g) (@lem6994684 A B t s f x g)). Qed.
Lemma lem6994686 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : term93 A B t s f x g.
Proof. exact (EQ_MP (@lem6993655 A B t s f x g) (@lem6994685 A B t s f x g)). Qed.
Lemma lem6994687 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> nat) : term92 A B t s f x g.
Proof. exact (EQ_MP (@lem6993483 A B t s f x g) (@lem6994686 A B t s f x g)). Qed.
Lemma lem6994688 {A B : Type'} (g : A -> nat) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term75 A B x f s) (h3 : @IN B x t) (h4 : term36 A B f s t) : term91 A B s f x g.
Proof. exact (@lem6994687 A B t s f x g (@lem6993424 A B x f s t h1 h2 h3 h4)). Qed.
Lemma lem6994689 {A B : Type'} (g : A -> nat) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term75 A B x f s) (h3 : @IN B x t) (h4 : term36 A B f s t) : (term60 A B s f x g) = (NUMERAL 0).
Proof. exact (@lem6993411 A B s f x g (@lem6994688 A B g x f s t h1 h2 h3 h4)). Qed.
Lemma lem6994690 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term74 A B t x f s) : term75 A B x f s.
Proof. exact (proj2 (@lem6993405 A B t x f s h1)). Qed.
Lemma lem6994691 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term74 A B t x f s) : @IN B x t.
Proof. exact (proj1 (@lem6993405 A B t x f s h1)). Qed.
Lemma lem6994692 {A B : Type'} (g : A -> nat) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term75 A B x f s) (h3 : @IN B x t) (h4 : term36 A B f s t) : (term75 A B x f s) = ((term60 A B s f x g) = (NUMERAL 0)).
Proof. exact (prop_ext (fun h5 : term75 A B x f s => @lem6994689 A B g x f s t h1 h2 h3 h4) (fun h5 : (term60 A B s f x g) = (NUMERAL 0) => @lem6993406 A B x f s h2)). Qed.
Lemma lem6994693 {A B : Type'} (g : A -> nat) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term75 A B x f s) (h3 : @IN B x t) (h4 : term36 A B f s t) : (term60 A B s f x g) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6994692 A B g x f s t h1 h2 h3 h4) (@lem6993406 A B x f s h2)). Qed.
Lemma lem6994694 {A B : Type'} (g : A -> nat) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term75 A B x f s) (h3 : @IN B x t) (h4 : term36 A B f s t) : (@IN B x t) = ((term60 A B s f x g) = (NUMERAL 0)).
Proof. exact (prop_ext (fun h5 : @IN B x t => @lem6994693 A B g x f s t h1 h2 h3 h4) (fun h5 : (term60 A B s f x g) = (NUMERAL 0) => @lem6993407 B x t h3)). Qed.
Lemma lem6994695 {A B : Type'} (g : A -> nat) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term75 A B x f s) (h3 : @IN B x t) (h4 : term36 A B f s t) : (term60 A B s f x g) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6994694 A B g x f s t h1 h2 h3 h4) (@lem6993407 B x t h3)). Qed.
Lemma lem6994696 {A B : Type'} (g : A -> nat) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term74 A B t x f s) (h3 : @IN B x t) (h4 : term36 A B f s t) : (term75 A B x f s) = ((term60 A B s f x g) = (NUMERAL 0)).
Proof. exact (prop_ext (fun h5 : term75 A B x f s => @lem6994695 A B g x f s t h1 h5 h3 h4) (fun h5 : (term60 A B s f x g) = (NUMERAL 0) => @lem6994690 A B t x f s h2)). Qed.
Lemma lem6994697 {A B : Type'} (g : A -> nat) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term74 A B t x f s) (h3 : @IN B x t) (h4 : term36 A B f s t) : (term60 A B s f x g) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6994696 A B g x f s t h1 h2 h3 h4) (@lem6994690 A B t x f s h2)). Qed.
Lemma lem6994698 {A B : Type'} (g : A -> nat) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term74 A B t x f s) (h3 : term36 A B f s t) : (@IN B x t) = ((term60 A B s f x g) = (NUMERAL 0)).
Proof. exact (prop_ext (fun h4 : @IN B x t => @lem6994697 A B g x f s t h1 h2 h4 h3) (fun h4 : (term60 A B s f x g) = (NUMERAL 0) => @lem6994691 A B t x f s h2)). Qed.
Lemma lem6994699 {A B : Type'} (g : A -> nat) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term74 A B t x f s) (h3 : term36 A B f s t) : (term60 A B s f x g) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6994698 A B g x f s t h1 h2 h3) (@lem6994691 A B t x f s h2)). Qed.
Lemma lem6994700 {A B : Type'} (x : B) (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term36 A B f s t) : term67 A B t s f x g.
Proof. exact (fun h0 : term74 A B t x f s => @lem6994699 A B g x f s t h1 h0 h2). Qed.
Lemma lem6994705 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term36 A B f s t) : term71 A B t s f g.
Proof. exact (fun x : B => @lem6994700 A B x g f s t h1 h2). Qed.
Lemma lem6994706 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term36 A B f s t) : term72 A B t s f g.
Proof. exact (EQ_MP (@lem6993404 A B g f s t h2) (@lem6994705 A B g f s t h1 h2)). Qed.
Lemma lem6994707 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term36 A B f s t) : (term42 A B t s f g) = (term38 A B s f g).
Proof. exact (@lem6993322 A B t s f g (@lem6994706 A B g f s t h1 h2)). Qed.
Lemma lem6994708 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : (@nsum A s g) = (term38 A B s f g)) (h3 : term36 A B f s t) : (term42 A B t s f g) = (@nsum A s g).
Proof. exact (EQ_MP (@lem6993304 A B t s f g h2) (@lem6994707 A B g f s t h1 h3)). Qed.
Lemma lem6994709 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term36 A B f s t) : term44 A B t f s g.
Proof. exact (fun h0 : (@nsum A s g) = (term38 A B s f g) => @lem6994708 A B g f s t h1 h0 h2). Qed.
Lemma lem6994710 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term36 A B f s t) : term43 A B t f s g.
Proof. exact (EQ_MP (@lem6993290 A B t f g s h1) (@lem6994709 A B g f s t h1 h2)). Qed.
Lemma lem6994711 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term36 A B f s t) : (term42 A B t s f g) = (@nsum A s g).
Proof. exact (@lem6994710 A B g f s t h1 h2 (@lem6993230 A B s f g)). Qed.
Lemma lem6994712 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term35 A B f s t) : term36 A B f s t.
Proof. exact (proj2 (@lem6993231 A B f s t h1)). Qed.
Lemma lem6994713 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term35 A B f s t) : @FINITE A s.
Proof. exact (proj1 (@lem6993231 A B f s t h1)). Qed.
Lemma lem6994714 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term36 A B f s t) : (term36 A B f s t) = ((term42 A B t s f g) = (@nsum A s g)).
Proof. exact (prop_ext (fun h3 : term36 A B f s t => @lem6994711 A B g f s t h1 h2) (fun h3 : (term42 A B t s f g) = (@nsum A s g) => @lem6993232 A B f s t h2)). Qed.
Lemma lem6994715 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term36 A B f s t) : (term42 A B t s f g) = (@nsum A s g).
Proof. exact (EQ_MP (@lem6994714 A B g f s t h1 h2) (@lem6993232 A B f s t h2)). Qed.
Lemma lem6994716 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term36 A B f s t) : (@FINITE A s) = ((term42 A B t s f g) = (@nsum A s g)).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem6994715 A B g f s t h1 h2) (fun h3 : (term42 A B t s f g) = (@nsum A s g) => @lem6993233 A s h1)). Qed.
Lemma lem6994717 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term36 A B f s t) : (term42 A B t s f g) = (@nsum A s g).
Proof. exact (EQ_MP (@lem6994716 A B g f s t h1 h2) (@lem6993233 A s h1)). Qed.
Lemma lem6994718 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term35 A B f s t) : (term36 A B f s t) = ((term42 A B t s f g) = (@nsum A s g)).
Proof. exact (prop_ext (fun h3 : term36 A B f s t => @lem6994717 A B g f s t h1 h3) (fun h3 : (term42 A B t s f g) = (@nsum A s g) => @lem6994712 A B f s t h2)). Qed.
Lemma lem6994719 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term35 A B f s t) : (term42 A B t s f g) = (@nsum A s g).
Proof. exact (EQ_MP (@lem6994718 A B g f s t h1 h2) (@lem6994712 A B f s t h2)). Qed.
Lemma lem6994720 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term35 A B f s t) : (@FINITE A s) = ((term42 A B t s f g) = (@nsum A s g)).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem6994719 A B g f s t h2 h1) (fun h2 : (term42 A B t s f g) = (@nsum A s g) => @lem6994713 A B f s t h1)). Qed.
Lemma lem6994721 {A B : Type'} (g : A -> nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term35 A B f s t) : (term42 A B t s f g) = (@nsum A s g).
Proof. exact (EQ_MP (@lem6994720 A B g f s t h1) (@lem6994713 A B f s t h1)). Qed.
Lemma lem6994722 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (g : A -> nat) : term237 A B t f s g.
Proof. exact (fun h0 : term35 A B f s t => @lem6994721 A B g f s t h0). Qed.
Lemma lem6994727 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> nat) : term238 A B f s g.
Proof. exact (fun t : B -> Prop => @lem6994722 A B t f s g). Qed.
Lemma lem6994732 {A B : Type'} (f : A -> B) (g : A -> nat) : term239 A B f g.
Proof. exact (fun s : A -> Prop => @lem6994727 A B f s g). Qed.
Lemma lem6994737 {A B : Type'} (f : A -> B) : term240 A B f.
Proof. exact (fun g : A -> nat => @lem6994732 A B f g). Qed.
Lemma lem6994742 {A B : Type'} : term241 A B.
Proof. exact (fun f : A -> B => @lem6994737 A B f). Qed.
