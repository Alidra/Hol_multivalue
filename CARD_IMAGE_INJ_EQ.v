Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_IMAGE_INJ_EQ_term_abbrevs.
Require Import CARD_IMAGE_INJ_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXTENSION_spec.
Require Import IN_IMAGE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18897_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Lemma lem4010102 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4010103 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4010104 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4010103 t1) (@lem4010102 t1)). Qed.
Lemma lem4010105 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4010104 t1 t2). Qed.
Lemma lem4010106 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4010107 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4010106 t1 t2) (@lem4010105 t1 t2)). Qed.
Lemma lem4010108 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4010107 t1 t2 t3). Qed.
Lemma lem4010109 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4010110 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4010109 t1 t2 t3) (@lem4010108 t1 t2 t3)). Qed.
Lemma lem4010111 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4010110 t1 t2 t3)). Qed.
Lemma lem4010112 {A B : Type'} (h1 : term7 A B) : term7 A B.
Proof. exact (h1). Qed.
Lemma lem4010113 {A B : Type'} (f : A -> B) (h1 : term7 A B) : term8 A B f.
Proof. exact (@lem4010112 A B h1 f). Qed.
Lemma lem4010114 {A B : Type'} (f : A -> B) : (term8 A B f) = (term9 A B f).
Proof. exact (eq_refl (term8 A B f)). Qed.
Lemma lem4010115 {A B : Type'} (f : A -> B) (h1 : term7 A B) : term9 A B f.
Proof. exact (EQ_MP (@lem4010114 A B f) (@lem4010113 A B f h1)). Qed.
Lemma lem4010116 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term7 A B) : term10 A B f s.
Proof. exact (@lem4010115 A B f h1 s). Qed.
Lemma lem4010117 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term10 A B f s) = (term11 A B f s).
Proof. exact (eq_refl (term10 A B f s)). Qed.
Lemma lem4010118 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term7 A B) : term11 A B f s.
Proof. exact (EQ_MP (@lem4010117 A B f s) (@lem4010116 A B f s h1)). Qed.
Lemma lem4010119 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term12 A B f s) : term12 A B f s.
Proof. exact (h1). Qed.
Lemma lem4010120 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term7 A B) (h2 : term12 A B f s) : (term13 A B f s) = (@CARD A s).
Proof. exact (@lem4010118 A B f s h1 (@lem4010119 A B f s h2)). Qed.
Lemma lem4010121 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term12 A B f s) : term14 A B f s.
Proof. exact (fun h0 : term7 A B => @lem4010120 A B f s h0 h1). Qed.
Lemma lem4010122 {A B : Type'} (h1 : term7 A B) : term7 A B.
Proof. exact (h1). Qed.
Lemma lem4010123 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term7 A B) (h2 : term12 A B f s) : (term13 A B f s) = (@CARD A s).
Proof. exact (@lem4010121 A B f s h2 (@lem4010122 A B h1)). Qed.
Lemma lem4010124 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term7 A B) : term11 A B f s.
Proof. exact (fun h0 : term12 A B f s => @lem4010123 A B f s h1 h0). Qed.
Lemma lem4010125 {A B : Type'} (f : A -> B) (h1 : term7 A B) : term9 A B f.
Proof. exact (fun s : A -> Prop => @lem4010124 A B f s h1). Qed.
Lemma lem4010126 {A B : Type'} (h1 : term7 A B) : term7 A B.
Proof. exact (fun f : A -> B => @lem4010125 A B f h1). Qed.
Lemma lem4010127 {A B : Type'} : term15 A B.
Proof. exact (fun h0 : term7 A B => @lem4010126 A B h0). Qed.
Lemma lem4010128 {A B : Type'} : term7 A B.
Proof. exact (@lem4010127 A B (@lem3996358 A B)). Qed.
Lemma lem4010129 {A B : Type'} (f : A -> B) : term8 A B f.
Proof. exact (@lem4010128 A B f). Qed.
Lemma lem4010130 {A B : Type'} (f : A -> B) : (term8 A B f) = (term9 A B f).
Proof. exact (eq_refl (term8 A B f)). Qed.
Lemma lem4010131 {A B : Type'} (f : A -> B) : term9 A B f.
Proof. exact (EQ_MP (@lem4010130 A B f) (@lem4010129 A B f)). Qed.
Lemma lem4010132 {A B : Type'} (f : A -> B) (s : A -> Prop) : term10 A B f s.
Proof. exact (@lem4010131 A B f s). Qed.
Lemma lem4010133 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term10 A B f s) = (term11 A B f s).
Proof. exact (eq_refl (term10 A B f s)). Qed.
Lemma lem4010145 {A B : Type'} (y : B) : term16 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem4010146 {A B : Type'} (y : B) : (term16 A B y) = (term17 A B y).
Proof. exact (eq_refl (term16 A B y)). Qed.
Lemma lem4010147 {A B : Type'} (y : B) : term17 A B y.
Proof. exact (EQ_MP (@lem4010146 A B y) (@lem4010145 A B y)). Qed.
Lemma lem4010148 {A B : Type'} (y : B) (s : A -> Prop) : term18 A B y s.
Proof. exact (@lem4010147 A B y s). Qed.
Lemma lem4010149 {A B : Type'} (y : B) (s : A -> Prop) : (term18 A B y s) = (term19 A B y s).
Proof. exact (eq_refl (term18 A B y s)). Qed.
Lemma lem4010150 {A B : Type'} (y : B) (s : A -> Prop) : term19 A B y s.
Proof. exact (EQ_MP (@lem4010149 A B y s) (@lem4010148 A B y s)). Qed.
Lemma lem4010151 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term20 A B y s f.
Proof. exact (@lem4010150 A B y s f). Qed.
Lemma lem4010152 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term20 A B y s f) = ((term21 A B y f s) = (term22 A B y f s)).
Proof. exact (eq_refl (term20 A B y s f)). Qed.
Lemma lem4010154 {A : Type'} (s : A -> Prop) : term23 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4010155 {A : Type'} (s : A -> Prop) : (term23 A s) = (term24 A s).
Proof. exact (eq_refl (term23 A s)). Qed.
Lemma lem4010156 {A : Type'} (s : A -> Prop) : term24 A s.
Proof. exact (EQ_MP (@lem4010155 A s) (@lem4010154 A s)). Qed.
Lemma lem4010157 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term25 A s t.
Proof. exact (@lem4010156 A s t). Qed.
Lemma lem4010158 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term25 A s t) = ((s = t) = (term26 A s t)).
Proof. exact (eq_refl (term25 A s t)). Qed.
Lemma lem4010160 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term27 A B t s f) : term27 A B t s f.
Proof. exact (h1). Qed.
Lemma lem4010161 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term28 A B t s f) : term28 A B t s f.
Proof. exact (h1). Qed.
Lemma lem4010162 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4010163 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term29 A B t s f) : term29 A B t s f.
Proof. exact (h1). Qed.
Lemma lem4010164 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term30 A B s f t.
Proof. exact (h1). Qed.
Lemma lem4010165 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B f s)) : t = (@IMAGE A B f s).
Proof. exact (h1). Qed.
Lemma lem4010166 {A B : Type'} (s : A -> Prop) : (term31 A B s) = (term31 A B s).
Proof. exact (eq_refl (term31 A B s)). Qed.
Lemma lem4010167 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B f s)) : (term32 A B s t) = (term33 A B f s).
Proof. exact (MK_COMB (@lem4010166 A B s) (@lem4010165 A B t f s h1)). Qed.
Lemma lem4010168 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term33 A B f s) = ((term13 A B f s) = (@CARD A s)).
Proof. exact (eq_refl (term33 A B f s)). Qed.
Lemma lem4010169 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term34 A B s t) = (term34 A B s t).
Proof. exact (eq_refl (term34 A B s t)). Qed.
Lemma lem4010170 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : ((term32 A B s t) = (term33 A B f s)) = ((term32 A B s t) = ((term13 A B f s) = (@CARD A s))).
Proof. exact (MK_COMB (@lem4010169 A B s t) (@lem4010168 A B f s)). Qed.
Lemma lem4010171 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term32 A B s t) = ((@CARD B t) = (@CARD A s)).
Proof. exact (eq_refl (term32 A B s t)). Qed.
Lemma lem4010172 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4010173 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term34 A B s t) = (term35 A B t s).
Proof. exact (MK_COMB (@lem4010172) (@lem4010171 A B t s)). Qed.
Lemma lem4010174 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term13 A B f s) = (@CARD A s)) = ((term13 A B f s) = (@CARD A s)).
Proof. exact (eq_refl ((term13 A B f s) = (@CARD A s))). Qed.
Lemma lem4010175 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : ((term32 A B s t) = ((term13 A B f s) = (@CARD A s))) = (((@CARD B t) = (@CARD A s)) = ((term13 A B f s) = (@CARD A s))).
Proof. exact (MK_COMB (@lem4010173 A B t s) (@lem4010174 A B f s)). Qed.
Lemma lem4010176 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : ((term32 A B s t) = (term33 A B f s)) = (((@CARD B t) = (@CARD A s)) = ((term13 A B f s) = (@CARD A s))).
Proof. exact (TRANS (@lem4010170 A B t f s) (@lem4010175 A B t f s)). Qed.
Lemma lem4010177 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B f s)) : ((@CARD B t) = (@CARD A s)) = ((term13 A B f s) = (@CARD A s)).
Proof. exact (EQ_MP (@lem4010176 A B t f s) (@lem4010167 A B t f s h1)). Qed.
Lemma lem4010178 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B f s)) : ((term13 A B f s) = (@CARD A s)) = ((@CARD B t) = (@CARD A s)).
Proof. exact (SYM (@lem4010177 A B t f s h1)). Qed.
Lemma lem4010182 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term26 A s t).
Proof. exact (EQ_MP (@lem4010158 A s t) (@lem4010157 A s t)). Qed.
Lemma lem4010183 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term26 B s t).
Proof. exact (@lem4010182 B s t). Qed.
Lemma lem4010184 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (t = (@IMAGE A B f s)) = (term36 A B t f s).
Proof. exact (@lem4010183 B t (@IMAGE A B f s)). Qed.
Lemma lem4010194 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term21 A B y f s) = (term22 A B y f s).
Proof. exact (EQ_MP (@lem4010152 A B y f s) (@lem4010151 A B y s f)). Qed.
Lemma lem4010195 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term21 A B y f s) = (term22 A B y f s).
Proof. exact (@lem4010194 A B y f s). Qed.
Lemma lem4010196 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term21 A B x f s) = (term22 A B x f s).
Proof. exact (@lem4010195 A B x f s). Qed.
Lemma lem4010207 {B : Type'} (x : B) (t : B -> Prop) : (term37 B x t) = (term37 B x t).
Proof. exact (eq_refl (term37 B x t)). Qed.
Lemma lem4010208 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((@IN B x t) = (term21 A B x f s)) = ((@IN B x t) = (term22 A B x f s)).
Proof. exact (MK_COMB (@lem4010207 B x t) (@lem4010196 A B x f s)). Qed.
Lemma lem4010213 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term38 A B t f s) = (term39 A B t f s).
Proof. exact (fun_ext (fun x : B => @lem4010208 A B t x f s)). Qed.
Lemma lem4010214 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4010215 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term36 A B t f s) = (term40 A B t f s).
Proof. exact (MK_COMB (@lem4010214 B) (@lem4010213 A B t f s)). Qed.
Lemma lem4010220 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (t = (@IMAGE A B f s)) = (term40 A B t f s).
Proof. exact (TRANS (@lem4010184 A B t f s) (@lem4010215 A B t f s)). Qed.
Lemma lem4010221 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term40 A B t f s) = (t = (@IMAGE A B f s)).
Proof. exact (SYM (@lem4010220 A B t f s)). Qed.
Lemma lem4010223 (p : Prop) : p = (term41 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4010224 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term40 A B t f s) = (term42 A B t f s).
Proof. exact (@lem4010223 (term40 A B t f s)). Qed.
Lemma lem4010225 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term42 A B t f s) = (term40 A B t f s).
Proof. exact (SYM (@lem4010224 A B t f s)). Qed.
Lemma lem4010226 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term43 A B t f s) : term43 A B t f s.
Proof. exact (h1). Qed.
Lemma lem4010229 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term44 A B t f s) : term44 A B t f s.
Proof. exact (h1). Qed.
Lemma lem4010230 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term45 A B t f s.
Proof. exact (fun h0 : term44 A B t f s => @lem4010229 A B t f s h0). Qed.
Lemma lem4010231 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term45 A B t f s) : term45 A B t f s.
Proof. exact (h1). Qed.
Lemma lem4010232 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term44 A B t f s) : term44 A B t f s.
Proof. exact (h1). Qed.
Lemma lem4010233 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term44 A B t f s) (h2 : term45 A B t f s) : term44 A B t f s.
Proof. exact (@lem4010231 A B t f s h2 (@lem4010232 A B t f s h1)). Qed.
Lemma lem4010234 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term44 A B t f s) : term46 A B t f s.
Proof. exact (fun h0 : term45 A B t f s => @lem4010233 A B t f s h1 h0). Qed.
Lemma lem4010235 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term45 A B t f s) : term45 A B t f s.
Proof. exact (h1). Qed.
Lemma lem4010236 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term44 A B t f s) (h2 : term45 A B t f s) : term44 A B t f s.
Proof. exact (@lem4010234 A B t f s h1 (@lem4010235 A B t f s h2)). Qed.
Lemma lem4010237 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term45 A B t f s) : term45 A B t f s.
Proof. exact (fun h0 : term44 A B t f s => @lem4010236 A B t f s h0 h1). Qed.
Lemma lem4010238 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term47 A B t f s.
Proof. exact (fun h0 : term45 A B t f s => @lem4010237 A B t f s h0). Qed.
Lemma lem4010241 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term45 A B t f s.
Proof. exact (@lem4010238 A B t f s (@lem4010230 A B t f s)). Qed.
Lemma lem4010242 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term45 A B t f s.
Proof. exact (@lem4010241 A B t f s). Qed.
Lemma lem4010276 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4010277 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term42 A B t f s) = (term48 A B t f s).
Proof. exact (@lem4010276 (term43 A B t f s)). Qed.
Lemma lem4010279 (t : Prop) : (term49 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4010280 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term48 A B t f s) = (term40 A B t f s).
Proof. exact (@lem4010279 (term40 A B t f s)). Qed.
Lemma lem4010285 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term42 A B t f s) = (term40 A B t f s).
Proof. exact (TRANS (@lem4010277 A B t f s) (@lem4010280 A B t f s)). Qed.
Lemma lem4010336 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term50 A B t s f) = (term50 A B t s f).
Proof. exact (eq_refl (term50 A B t s f)). Qed.
Lemma lem4010337 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term51 A B t f s) = (term52 A B t f s).
Proof. exact (MK_COMB (@lem4010336 A B t s f) (@lem4010285 A B t f s)). Qed.
Lemma lem4010340 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term53 A B s f t) = (term53 A B s f t).
Proof. exact (eq_refl (term53 A B s f t)). Qed.
Lemma lem4010341 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term54 A B t f s) = (term55 A B t f s).
Proof. exact (MK_COMB (@lem4010340 A B s f t) (@lem4010337 A B t f s)). Qed.
Lemma lem4010344 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (eq_refl (term56 A s)). Qed.
Lemma lem4010345 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term44 A B t f s) = (term57 A B t f s).
Proof. exact (MK_COMB (@lem4010344 A s) (@lem4010341 A B t f s)). Qed.
Lemma lem4010348 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term58 A B f s) = (term59 A B f s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4010345 A B t f s)). Qed.
Lemma lem4010349 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4010350 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term60 A B f s) = (term61 A B f s).
Proof. exact (MK_COMB (@lem4010349 B) (@lem4010348 A B f s)). Qed.
Lemma lem4010355 {A B : Type'} (s : A -> Prop) : (term62 A B s) = (term63 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem4010350 A B f s)). Qed.
Lemma lem4010356 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4010357 {A B : Type'} (s : A -> Prop) : (term64 A B s) = (term65 A B s).
Proof. exact (MK_COMB (@lem4010356 A B) (@lem4010355 A B s)). Qed.
Lemma lem4010362 {A B : Type'} : (term66 A B) = (term67 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4010357 A B s)). Qed.
Lemma lem4010363 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4010372 {A B : Type'} : (term68 A B) = (term69 A B).
Proof. exact (MK_COMB (@lem4010363 A) (@lem4010362 A B)). Qed.
Lemma lem4010377 {A B : Type'} (x : B) (f : A -> B) (x' : A) (s : A -> Prop) : (term70 A B x f x' s) = (term70 A B x f x' s).
Proof. exact (eq_refl (term70 A B x f x' s)). Qed.
Lemma lem4010378 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term71 A B x f s) = (term71 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4010377 A B x f x' s)). Qed.
Lemma lem4010379 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4010380 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term22 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem4010379 A) (@lem4010378 A B x f s)). Qed.
Lemma lem4010383 {B : Type'} (x : B) (t : B -> Prop) : (term37 B x t) = (term37 B x t).
Proof. exact (eq_refl (term37 B x t)). Qed.
Lemma lem4010384 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((@IN B x t) = (term22 A B x f s)) = ((@IN B x t) = (term22 A B x f s)).
Proof. exact (MK_COMB (@lem4010383 B x t) (@lem4010380 A B x f s)). Qed.
Lemma lem4010385 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term39 A B t f s) = (term39 A B t f s).
Proof. exact (fun_ext (fun x : B => @lem4010384 A B t x f s)). Qed.
Lemma lem4010386 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4010387 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term40 A B t f s) = (term40 A B t f s).
Proof. exact (MK_COMB (@lem4010386 B) (@lem4010385 A B t f s)). Qed.
Lemma lem4010392 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term72 A B s f x y) = (term72 A B s f x y).
Proof. exact (eq_refl (term72 A B s f x y)). Qed.
Lemma lem4010393 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term73 A B s f y) = (term73 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4010392 A B s f x y)). Qed.
Lemma lem4010394 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem4010395 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term74 A B s f y) = (term74 A B s f y).
Proof. exact (MK_COMB (@lem4010394 A) (@lem4010393 A B s f y)). Qed.
Lemma lem4010398 {B : Type'} (y : B) (t : B -> Prop) : (term75 B y t) = (term75 B y t).
Proof. exact (eq_refl (term75 B y t)). Qed.
Lemma lem4010399 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term76 A B t s f y) = (term76 A B t s f y).
Proof. exact (MK_COMB (@lem4010398 B y t) (@lem4010395 A B s f y)). Qed.
Lemma lem4010400 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term77 A B t s f) = (term77 A B t s f).
Proof. exact (fun_ext (fun y : B => @lem4010399 A B t s f y)). Qed.
Lemma lem4010401 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4010402 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term29 A B t s f) = (term29 A B t s f).
Proof. exact (MK_COMB (@lem4010401 B) (@lem4010400 A B t s f)). Qed.
Lemma lem4010403 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4010404 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term50 A B t s f) = (term50 A B t s f).
Proof. exact (MK_COMB (@lem4010403) (@lem4010402 A B t s f)). Qed.
Lemma lem4010405 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term52 A B t f s) = (term52 A B t f s).
Proof. exact (MK_COMB (@lem4010404 A B t s f) (@lem4010387 A B t f s)). Qed.
Lemma lem4010410 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term78 A B s f x t) = (term78 A B s f x t).
Proof. exact (eq_refl (term78 A B s f x t)). Qed.
Lemma lem4010411 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term79 A B s f t) = (term79 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem4010410 A B s f x t)). Qed.
Lemma lem4010412 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4010413 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term30 A B s f t) = (term30 A B s f t).
Proof. exact (MK_COMB (@lem4010412 A) (@lem4010411 A B s f t)). Qed.
Lemma lem4010414 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4010415 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term53 A B s f t) = (term53 A B s f t).
Proof. exact (MK_COMB (@lem4010414) (@lem4010413 A B s f t)). Qed.
Lemma lem4010416 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term55 A B t f s) = (term55 A B t f s).
Proof. exact (MK_COMB (@lem4010415 A B s f t) (@lem4010405 A B t f s)). Qed.
Lemma lem4010419 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (eq_refl (term56 A s)). Qed.
Lemma lem4010420 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term57 A B t f s) = (term57 A B t f s).
Proof. exact (MK_COMB (@lem4010419 A s) (@lem4010416 A B t f s)). Qed.
Lemma lem4010421 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term59 A B f s) = (term59 A B f s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4010420 A B t f s)). Qed.
Lemma lem4010422 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4010423 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term61 A B f s) = (term61 A B f s).
Proof. exact (MK_COMB (@lem4010422 B) (@lem4010421 A B f s)). Qed.
Lemma lem4010424 {A B : Type'} (s : A -> Prop) : (term63 A B s) = (term63 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem4010423 A B f s)). Qed.
Lemma lem4010425 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4010426 {A B : Type'} (s : A -> Prop) : (term65 A B s) = (term65 A B s).
Proof. exact (MK_COMB (@lem4010425 A B) (@lem4010424 A B s)). Qed.
Lemma lem4010427 {A B : Type'} : (term67 A B) = (term67 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4010426 A B s)). Qed.
Lemma lem4010428 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4010429 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (MK_COMB (@lem4010428 A) (@lem4010427 A B)). Qed.
Lemma lem4010488 {A B : Type'} : (term68 A B) = (term69 A B).
Proof. exact (TRANS (@lem4010372 A B) (@lem4010429 A B)). Qed.
Lemma lem4010489 {A B : Type'} : (term69 A B) = (term68 A B).
Proof. exact (SYM (@lem4010488 A B)). Qed.
Lemma lem4010491 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term30 A B s f t.
Proof. exact (h1). Qed.
Lemma lem4010492 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term29 A B t s f) : term29 A B t s f.
Proof. exact (h1). Qed.
Lemma lem4010494 (p : Prop) : p = (term41 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4010495 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((@IN B x t) = (term22 A B x f s)) = (term80 A B t x f s).
Proof. exact (@lem4010494 ((@IN B x t) = (term22 A B x f s))). Qed.
Lemma lem4010496 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term80 A B t x f s) = ((@IN B x t) = (term22 A B x f s)).
Proof. exact (SYM (@lem4010495 A B t x f s)). Qed.
Lemma lem4010497 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term81 A B t x f s) : term81 A B t x f s.
Proof. exact (h1). Qed.
Lemma lem4010510 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term78 A B s f x t) = (term82 A B s f x t).
Proof. exact (@lem17265 (@IN A x s) (term83 A B f x t)). Qed.
Lemma lem4010511 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term79 A B s f t) = (term84 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem4010510 A B s f x t)). Qed.
Lemma lem4010512 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4010565 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term30 A B s f t) = (term85 A B s f t).
Proof. exact (MK_COMB (@lem4010512 A) (@lem4010511 A B s f t)). Qed.
Lemma lem4010566 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term85 A B s f t.
Proof. exact (EQ_MP (@lem4010565 A B s f t) (@lem4010491 A B s f t h1)). Qed.
Lemma lem4010576 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term86 A B s f x y) = (term87 A B s f x y).
Proof. exact (@lem17045 (@IN A x s) ((f x) = y)). Qed.
Lemma lem4010581 {A : Type'} (x' : A) (x : A) : (x' = x) = (x' = x).
Proof. exact (eq_refl (x' = x)). Qed.
Lemma lem4010582 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term88 A B s f y x) = (term72 A B s f x y).
Proof. exact (eq_refl (term88 A B s f y x)). Qed.
Lemma lem4010583 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) : (term88 A B s f y x') = (term72 A B s f x' y).
Proof. exact (eq_refl (term88 A B s f y x')). Qed.
Lemma lem4010584 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) : (term86 A B s f x' y) = (term87 A B s f x' y).
Proof. exact (@lem4010576 A B s f x' y). Qed.
Lemma lem4010585 {A : Type'} (P : A -> Prop) : (@ex1 A P) = (term89 A P).
Proof. exact (@lem18897 A P). Qed.
Lemma lem4010586 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term74 A B s f y) = (term90 A B s f y).
Proof. exact (@lem4010585 A (term73 A B s f y)). Qed.
Lemma lem4010587 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4010588 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) : (term91 A B s f y x') = (term86 A B s f x' y).
Proof. exact (MK_COMB (@lem4010587) (@lem4010583 A B s f x' y)). Qed.
Lemma lem4010589 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) : (term91 A B s f y x') = (term87 A B s f x' y).
Proof. exact (TRANS (@lem4010588 A B s f x' y) (@lem4010584 A B s f x' y)). Qed.
Lemma lem4010590 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4010591 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) : (term92 A B s f y x') = (term93 A B s f x' y).
Proof. exact (MK_COMB (@lem4010590) (@lem4010589 A B s f x' y)). Qed.
Lemma lem4010592 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term94 A B s f y x' x) = (term95 A B s f y x' x).
Proof. exact (MK_COMB (@lem4010591 A B s f x' y) (@lem4010581 A x' x)). Qed.
Lemma lem4010593 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4010594 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term91 A B s f y x) = (term86 A B s f x y).
Proof. exact (MK_COMB (@lem4010593) (@lem4010582 A B s f x y)). Qed.
Lemma lem4010595 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term91 A B s f y x) = (term87 A B s f x y).
Proof. exact (TRANS (@lem4010594 A B s f x y) (@lem4010576 A B s f x y)). Qed.
Lemma lem4010596 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4010597 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term92 A B s f y x) = (term93 A B s f x y).
Proof. exact (MK_COMB (@lem4010596) (@lem4010595 A B s f x y)). Qed.
Lemma lem4010598 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term96 A B s f y x' x) = (term97 A B s f y x' x).
Proof. exact (MK_COMB (@lem4010597 A B s f x y) (@lem4010592 A B s f y x' x)). Qed.
Lemma lem4010599 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term98 A B s f y x) = (term99 A B s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4010598 A B s f y x' x)). Qed.
Lemma lem4010600 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4010601 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term100 A B s f y x) = (term101 A B s f y x).
Proof. exact (MK_COMB (@lem4010600 A) (@lem4010599 A B s f y x)). Qed.
Lemma lem4010602 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term102 A B s f y) = (term103 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4010601 A B s f y x)). Qed.
Lemma lem4010603 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4010604 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term104 A B s f y) = (term105 A B s f y).
Proof. exact (MK_COMB (@lem4010603 A) (@lem4010602 A B s f y)). Qed.
Lemma lem4010605 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term88 A B s f y x) = (term72 A B s f x y).
Proof. exact (eq_refl (term88 A B s f y x)). Qed.
Lemma lem4010606 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term106 A B s f y) = (term73 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4010605 A B s f x y)). Qed.
Lemma lem4010607 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4010608 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term107 A B s f y) = (term108 A B s f y).
Proof. exact (MK_COMB (@lem4010607 A) (@lem4010606 A B s f y)). Qed.
Lemma lem4010609 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4010610 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term109 A B s f y) = (term110 A B s f y).
Proof. exact (MK_COMB (@lem4010609) (@lem4010608 A B s f y)). Qed.
Lemma lem4010611 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term90 A B s f y) = (term111 A B s f y).
Proof. exact (MK_COMB (@lem4010610 A B s f y) (@lem4010604 A B s f y)). Qed.
Lemma lem4010612 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term74 A B s f y) = (term111 A B s f y).
Proof. exact (TRANS (@lem4010586 A B s f y) (@lem4010611 A B s f y)). Qed.
Lemma lem4010614 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4010615 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term113 A B t s f y) = (term114 A B t s f y).
Proof. exact (MK_COMB (@lem4010614 B y t) (@lem4010612 A B s f y)). Qed.
Lemma lem4010616 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term76 A B t s f y) = (term113 A B t s f y).
Proof. exact (@lem17265 (@IN B y t) (term74 A B s f y)). Qed.
Lemma lem4010617 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term76 A B t s f y) = (term114 A B t s f y).
Proof. exact (TRANS (@lem4010616 A B t s f y) (@lem4010615 A B t s f y)). Qed.
Lemma lem4010618 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term77 A B t s f) = (term115 A B t s f).
Proof. exact (fun_ext (fun y : B => @lem4010617 A B t s f y)). Qed.
Lemma lem4010619 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4010620 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term29 A B t s f) = (term116 A B t s f).
Proof. exact (MK_COMB (@lem4010619 B) (@lem4010618 A B t s f)). Qed.
Lemma lem4010722 {A : Type'} (P : Prop) (Q : A -> Prop) : (term117 A P Q) = (term118 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem4010723 {A : Type'} (P : Prop) (Q : A -> Prop) : (term117 A P Q) = (term118 A P Q).
Proof. exact (@lem4010722 A P Q). Qed.
Lemma lem4010724 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term119 A B s f y x) = (term120 A B s f y x).
Proof. exact (@lem4010723 A (term87 A B s f x y) (term121 A B s f y x)). Qed.
Lemma lem4010725 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term122 A B s f y x x') = (term95 A B s f y x' x).
Proof. exact (eq_refl (term122 A B s f y x x')). Qed.
Lemma lem4010726 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term93 A B s f x y) = (term93 A B s f x y).
Proof. exact (eq_refl (term93 A B s f x y)). Qed.
Lemma lem4010727 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term123 A B s f y x x') = (term97 A B s f y x' x).
Proof. exact (MK_COMB (@lem4010726 A B s f x y) (@lem4010725 A B s f y x' x)). Qed.
Lemma lem4010728 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term124 A B s f y x) = (term99 A B s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4010727 A B s f y x' x)). Qed.
Lemma lem4010729 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4010730 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term119 A B s f y x) = (term101 A B s f y x).
Proof. exact (MK_COMB (@lem4010729 A) (@lem4010728 A B s f y x)). Qed.
Lemma lem4010731 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4010732 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term125 A B s f y x) = (term126 A B s f y x).
Proof. exact (MK_COMB (@lem4010731) (@lem4010730 A B s f y x)). Qed.
Lemma lem4010733 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term122 A B s f y x x') = (term95 A B s f y x' x).
Proof. exact (eq_refl (term122 A B s f y x x')). Qed.
Lemma lem4010734 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term127 A B s f y x) = (term121 A B s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4010733 A B s f y x' x)). Qed.
Lemma lem4010735 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4010736 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term128 A B s f y x) = (term129 A B s f y x).
Proof. exact (MK_COMB (@lem4010735 A) (@lem4010734 A B s f y x)). Qed.
Lemma lem4010737 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term93 A B s f x y) = (term93 A B s f x y).
Proof. exact (eq_refl (term93 A B s f x y)). Qed.
Lemma lem4010738 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term120 A B s f y x) = (term130 A B s f y x).
Proof. exact (MK_COMB (@lem4010737 A B s f x y) (@lem4010736 A B s f y x)). Qed.
Lemma lem4010739 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : ((term119 A B s f y x) = (term120 A B s f y x)) = ((term101 A B s f y x) = (term130 A B s f y x)).
Proof. exact (MK_COMB (@lem4010732 A B s f y x) (@lem4010738 A B s f y x)). Qed.
Lemma lem4010740 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term101 A B s f y x) = (term130 A B s f y x).
Proof. exact (EQ_MP (@lem4010739 A B s f y x) (@lem4010724 A B s f y x)). Qed.
Lemma lem4010789 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term103 A B s f y) = (term131 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4010740 A B s f y x)). Qed.
Lemma lem4010790 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4010791 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term105 A B s f y) = (term132 A B s f y).
Proof. exact (MK_COMB (@lem4010790 A) (@lem4010789 A B s f y)). Qed.
Lemma lem4010840 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term110 A B s f y) = (term110 A B s f y).
Proof. exact (eq_refl (term110 A B s f y)). Qed.
Lemma lem4010841 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term111 A B s f y) = (term133 A B s f y).
Proof. exact (MK_COMB (@lem4010840 A B s f y) (@lem4010791 A B s f y)). Qed.
Lemma lem4010842 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4010843 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term114 A B t s f y) = (term134 A B t s f y).
Proof. exact (MK_COMB (@lem4010842 B y t) (@lem4010841 A B s f y)). Qed.
Lemma lem4010844 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term115 A B t s f) = (term135 A B t s f).
Proof. exact (fun_ext (fun y : B => @lem4010843 A B t s f y)). Qed.
Lemma lem4010845 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4010846 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term116 A B t s f) = (term136 A B t s f).
Proof. exact (MK_COMB (@lem4010845 B) (@lem4010844 A B t s f)). Qed.
Lemma lem4010896 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4010897 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (@lem4010896 A P Q). Qed.
Lemma lem4010898 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term139 A B s f y) = (term140 A B s f y).
Proof. exact (@lem4010897 A (term73 A B s f y) (term132 A B s f y)). Qed.
Lemma lem4010899 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term88 A B s f y x) = (term72 A B s f x y).
Proof. exact (eq_refl (term88 A B s f y x)). Qed.
Lemma lem4010900 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term106 A B s f y) = (term73 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4010899 A B s f x y)). Qed.
Lemma lem4010901 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4010902 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term107 A B s f y) = (term108 A B s f y).
Proof. exact (MK_COMB (@lem4010901 A) (@lem4010900 A B s f y)). Qed.
Lemma lem4010903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4010904 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term109 A B s f y) = (term110 A B s f y).
Proof. exact (MK_COMB (@lem4010903) (@lem4010902 A B s f y)). Qed.
Lemma lem4010905 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term132 A B s f y) = (term132 A B s f y).
Proof. exact (eq_refl (term132 A B s f y)). Qed.
Lemma lem4010906 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term139 A B s f y) = (term133 A B s f y).
Proof. exact (MK_COMB (@lem4010904 A B s f y) (@lem4010905 A B s f y)). Qed.
Lemma lem4010907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4010908 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term141 A B s f y) = (term142 A B s f y).
Proof. exact (MK_COMB (@lem4010907) (@lem4010906 A B s f y)). Qed.
Lemma lem4010909 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term88 A B s f y x) = (term72 A B s f x y).
Proof. exact (eq_refl (term88 A B s f y x)). Qed.
Lemma lem4010910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4010911 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term143 A B s f y x) = (term144 A B s f x y).
Proof. exact (MK_COMB (@lem4010910) (@lem4010909 A B s f x y)). Qed.
Lemma lem4010912 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term132 A B s f y) = (term132 A B s f y).
Proof. exact (eq_refl (term132 A B s f y)). Qed.
Lemma lem4010913 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (y : B) : (term145 A B x s f y) = (term146 A B x s f y).
Proof. exact (MK_COMB (@lem4010911 A B s f x y) (@lem4010912 A B s f y)). Qed.
Lemma lem4010914 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term147 A B s f y) = (term148 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4010913 A B x s f y)). Qed.
Lemma lem4010915 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4010916 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term140 A B s f y) = (term149 A B s f y).
Proof. exact (MK_COMB (@lem4010915 A) (@lem4010914 A B s f y)). Qed.
Lemma lem4010917 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : ((term139 A B s f y) = (term140 A B s f y)) = ((term133 A B s f y) = (term149 A B s f y)).
Proof. exact (MK_COMB (@lem4010908 A B s f y) (@lem4010916 A B s f y)). Qed.
Lemma lem4010918 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term133 A B s f y) = (term149 A B s f y).
Proof. exact (EQ_MP (@lem4010917 A B s f y) (@lem4010898 A B s f y)). Qed.
Lemma lem4010919 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4010920 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term134 A B t s f y) = (term150 A B t s f y).
Proof. exact (MK_COMB (@lem4010919 B y t) (@lem4010918 A B s f y)). Qed.
Lemma lem4010922 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4010923 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (@lem4010922 A P Q). Qed.
Lemma lem4010924 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term153 A B t s f y) = (term154 A B t s f y).
Proof. exact (@lem4010923 A (term155 B y t) (term148 A B s f y)). Qed.
Lemma lem4010925 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (y : B) : (term156 A B s f y x) = (term146 A B x s f y).
Proof. exact (eq_refl (term156 A B s f y x)). Qed.
Lemma lem4010926 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term157 A B s f y) = (term148 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4010925 A B x s f y)). Qed.
Lemma lem4010927 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4010928 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term158 A B s f y) = (term149 A B s f y).
Proof. exact (MK_COMB (@lem4010927 A) (@lem4010926 A B s f y)). Qed.
Lemma lem4010929 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4010930 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term153 A B t s f y) = (term150 A B t s f y).
Proof. exact (MK_COMB (@lem4010929 B y t) (@lem4010928 A B s f y)). Qed.
Lemma lem4010931 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4010932 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term159 A B t s f y) = (term160 A B t s f y).
Proof. exact (MK_COMB (@lem4010931) (@lem4010930 A B t s f y)). Qed.
Lemma lem4010933 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (y : B) : (term156 A B s f y x) = (term146 A B x s f y).
Proof. exact (eq_refl (term156 A B s f y x)). Qed.
Lemma lem4010934 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4010935 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) (y : B) : (term161 A B t s f y x) = (term162 A B t x s f y).
Proof. exact (MK_COMB (@lem4010934 B y t) (@lem4010933 A B x s f y)). Qed.
Lemma lem4010936 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term163 A B t s f y) = (term164 A B t s f y).
Proof. exact (fun_ext (fun x : A => @lem4010935 A B t x s f y)). Qed.
Lemma lem4010937 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4010938 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term154 A B t s f y) = (term165 A B t s f y).
Proof. exact (MK_COMB (@lem4010937 A) (@lem4010936 A B t s f y)). Qed.
Lemma lem4010939 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : ((term153 A B t s f y) = (term154 A B t s f y)) = ((term150 A B t s f y) = (term165 A B t s f y)).
Proof. exact (MK_COMB (@lem4010932 A B t s f y) (@lem4010938 A B t s f y)). Qed.
Lemma lem4010940 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term150 A B t s f y) = (term165 A B t s f y).
Proof. exact (EQ_MP (@lem4010939 A B t s f y) (@lem4010924 A B t s f y)). Qed.
Lemma lem4010941 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term134 A B t s f y) = (term165 A B t s f y).
Proof. exact (TRANS (@lem4010920 A B t s f y) (@lem4010940 A B t s f y)). Qed.
Lemma lem4010942 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term135 A B t s f) = (term166 A B t s f).
Proof. exact (fun_ext (fun y : B => @lem4010941 A B t s f y)). Qed.
Lemma lem4010943 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4010944 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term136 A B t s f) = (term167 A B t s f).
Proof. exact (MK_COMB (@lem4010943 B) (@lem4010942 A B t s f)). Qed.
Lemma lem4010946 {A B : Type'} (P : type1413 A B) : (term168 A B P) = (term169 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4010947 {A B : Type'} (P : type1470 A B) : (term170 A B P) = (term171 A B P).
Proof. exact (@lem4010946 B A P). Qed.
Lemma lem4010948 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term172 A B t s f) = (term173 A B t s f).
Proof. exact (@lem4010947 A B (term174 A B t s f)). Qed.
Lemma lem4010949 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term175 A B t s f y) = (term164 A B t s f y).
Proof. exact (eq_refl (term175 A B t s f y)). Qed.
Lemma lem4010950 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4010951 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term176 A B t s f y x) = (term177 A B t s f y x).
Proof. exact (MK_COMB (@lem4010949 A B t s f y) (@lem4010950 A x)). Qed.
Lemma lem4010952 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) (y : B) : (term177 A B t s f y x) = (term162 A B t x s f y).
Proof. exact (eq_refl (term177 A B t s f y x)). Qed.
Lemma lem4010953 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) (y : B) : (term176 A B t s f y x) = (term162 A B t x s f y).
Proof. exact (TRANS (@lem4010951 A B t s f y x) (@lem4010952 A B t x s f y)). Qed.
Lemma lem4010954 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term178 A B t s f y) = (term164 A B t s f y).
Proof. exact (fun_ext (fun x : A => @lem4010953 A B t x s f y)). Qed.
Lemma lem4010955 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4010956 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term179 A B t s f y) = (term165 A B t s f y).
Proof. exact (MK_COMB (@lem4010955 A) (@lem4010954 A B t s f y)). Qed.
Lemma lem4010957 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term180 A B t s f) = (term166 A B t s f).
Proof. exact (fun_ext (fun y : B => @lem4010956 A B t s f y)). Qed.
Lemma lem4010958 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4010959 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term172 A B t s f) = (term167 A B t s f).
Proof. exact (MK_COMB (@lem4010958 B) (@lem4010957 A B t s f)). Qed.
Lemma lem4010960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4010961 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term181 A B t s f) = (term182 A B t s f).
Proof. exact (MK_COMB (@lem4010960) (@lem4010959 A B t s f)). Qed.
Lemma lem4010962 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term175 A B t s f y) = (term164 A B t s f y).
Proof. exact (eq_refl (term175 A B t s f y)). Qed.
Lemma lem4010963 {A B : Type'} (x : B -> A) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem4010964 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B -> A) (y : B) : (term183 A B t s f x y) = (term184 A B t s f x y).
Proof. exact (MK_COMB (@lem4010962 A B t s f y) (@lem4010963 A B x y)). Qed.
Lemma lem4010965 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term184 A B t s f x y) = (term185 A B t x s f y).
Proof. exact (eq_refl (term184 A B t s f x y)). Qed.
Lemma lem4010966 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term183 A B t s f x y) = (term185 A B t x s f y).
Proof. exact (TRANS (@lem4010964 A B t s f x y) (@lem4010965 A B t x s f y)). Qed.
Lemma lem4010967 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) : (term186 A B t s f x) = (term187 A B t x s f).
Proof. exact (fun_ext (fun y : B => @lem4010966 A B t x s f y)). Qed.
Lemma lem4010968 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4010969 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) : (term188 A B t s f x) = (term189 A B t x s f).
Proof. exact (MK_COMB (@lem4010968 B) (@lem4010967 A B t x s f)). Qed.
Lemma lem4010970 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term190 A B t s f) = (term191 A B t s f).
Proof. exact (fun_ext (fun x : B -> A => @lem4010969 A B t x s f)). Qed.
Lemma lem4010971 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem4010972 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term173 A B t s f) = (term192 A B t s f).
Proof. exact (MK_COMB (@lem4010971 A B) (@lem4010970 A B t s f)). Qed.
Lemma lem4010973 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : ((term172 A B t s f) = (term173 A B t s f)) = ((term167 A B t s f) = (term192 A B t s f)).
Proof. exact (MK_COMB (@lem4010961 A B t s f) (@lem4010972 A B t s f)). Qed.
Lemma lem4010974 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term167 A B t s f) = (term192 A B t s f).
Proof. exact (EQ_MP (@lem4010973 A B t s f) (@lem4010948 A B t s f)). Qed.
Lemma lem4010975 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term136 A B t s f) = (term192 A B t s f).
Proof. exact (TRANS (@lem4010944 A B t s f) (@lem4010974 A B t s f)). Qed.
Lemma lem4010976 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term116 A B t s f) = (term192 A B t s f).
Proof. exact (TRANS (@lem4010846 A B t s f) (@lem4010975 A B t s f)). Qed.
Lemma lem4010977 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term29 A B t s f) = (term192 A B t s f).
Proof. exact (TRANS (@lem4010620 A B t s f) (@lem4010976 A B t s f)). Qed.
Lemma lem4010978 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term29 A B t s f) : term192 A B t s f.
Proof. exact (EQ_MP (@lem4010977 A B t s f) (@lem4010492 A B t s f h1)). Qed.
Lemma lem4010989 {A B : Type'} (x : B) (f : A -> B) (x' : A) (s : A -> Prop) : (term193 A B x f x' s) = (term194 A B x f x' s).
Proof. exact (@lem17045 (x = (f x')) (@IN A x' s)). Qed.
Lemma lem4010992 {A B : Type'} (x : B) (f : A -> B) (x' : A) (s : A -> Prop) : (term70 A B x f x' s) = (term70 A B x f x' s).
Proof. exact (eq_refl (term70 A B x f x' s)). Qed.
Lemma lem4010993 {A : Type'} (P : A -> Prop) : (term195 A P) = (term196 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4010994 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term197 A B x f s) = (term198 A B x f s).
Proof. exact (@lem4010993 A (term71 A B x f s)). Qed.
Lemma lem4010995 {A B : Type'} (x : B) (f : A -> B) (x' : A) (s : A -> Prop) : (term199 A B x f s x') = (term70 A B x f x' s).
Proof. exact (eq_refl (term199 A B x f s x')). Qed.
Lemma lem4010996 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4010997 {A B : Type'} (x : B) (f : A -> B) (x' : A) (s : A -> Prop) : (term200 A B x f s x') = (term193 A B x f x' s).
Proof. exact (MK_COMB (@lem4010996) (@lem4010995 A B x f x' s)). Qed.
Lemma lem4010998 {A B : Type'} (x : B) (f : A -> B) (x' : A) (s : A -> Prop) : (term200 A B x f s x') = (term194 A B x f x' s).
Proof. exact (TRANS (@lem4010997 A B x f x' s) (@lem4010989 A B x f x' s)). Qed.
Lemma lem4010999 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term201 A B x f s) = (term202 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4010998 A B x f x' s)). Qed.
Lemma lem4011000 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011001 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term198 A B x f s) = (term203 A B x f s).
Proof. exact (MK_COMB (@lem4011000 A) (@lem4010999 A B x f s)). Qed.
Lemma lem4011002 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term197 A B x f s) = (term203 A B x f s).
Proof. exact (TRANS (@lem4010994 A B x f s) (@lem4011001 A B x f s)). Qed.
Lemma lem4011003 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term71 A B x f s) = (term71 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4010992 A B x f x' s)). Qed.
Lemma lem4011004 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4011005 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term22 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem4011004 A) (@lem4011003 A B x f s)). Qed.
Lemma lem4011007 {B : Type'} (x : B) (t : B -> Prop) : (term204 B x t) = (term204 B x t).
Proof. exact (eq_refl (term204 B x t)). Qed.
Lemma lem4011008 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term205 A B t x f s) = (term205 A B t x f s).
Proof. exact (MK_COMB (@lem4011007 B x t) (@lem4011005 A B x f s)). Qed.
Lemma lem4011010 {B : Type'} (x : B) (t : B -> Prop) : (term206 B x t) = (term206 B x t).
Proof. exact (eq_refl (term206 B x t)). Qed.
Lemma lem4011011 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term207 A B t x f s) = (term208 A B t x f s).
Proof. exact (MK_COMB (@lem4011010 B x t) (@lem4011002 A B x f s)). Qed.
Lemma lem4011012 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4011013 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term209 A B t x f s) = (term210 A B t x f s).
Proof. exact (MK_COMB (@lem4011012) (@lem4011011 A B t x f s)). Qed.
Lemma lem4011014 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term211 A B t x f s) = (term212 A B t x f s).
Proof. exact (MK_COMB (@lem4011013 A B t x f s) (@lem4011008 A B t x f s)). Qed.
Lemma lem4011015 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term81 A B t x f s) = (term211 A B t x f s).
Proof. exact (@lem17646 (@IN B x t) (term22 A B x f s)). Qed.
Lemma lem4011016 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term81 A B t x f s) = (term212 A B t x f s).
Proof. exact (TRANS (@lem4011015 A B t x f s) (@lem4011014 A B t x f s)). Qed.
Lemma lem4011115 {A : Type'} (P : Prop) (Q : A -> Prop) : (term213 A P Q) = (term214 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4011116 {A : Type'} (P : Prop) (Q : A -> Prop) : (term213 A P Q) = (term214 A P Q).
Proof. exact (@lem4011115 A P Q). Qed.
Lemma lem4011117 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term215 A B t x f s) = (term216 A B t x f s).
Proof. exact (@lem4011116 A (term155 B x t) (term71 A B x f s)). Qed.
Lemma lem4011118 {A B : Type'} (x : B) (f : A -> B) (x' : A) (s : A -> Prop) : (term199 A B x f s x') = (term70 A B x f x' s).
Proof. exact (eq_refl (term199 A B x f s x')). Qed.
Lemma lem4011119 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term217 A B x f s) = (term71 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4011118 A B x f x' s)). Qed.
Lemma lem4011120 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4011121 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term218 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem4011120 A) (@lem4011119 A B x f s)). Qed.
Lemma lem4011122 {B : Type'} (x : B) (t : B -> Prop) : (term204 B x t) = (term204 B x t).
Proof. exact (eq_refl (term204 B x t)). Qed.
Lemma lem4011123 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term215 A B t x f s) = (term205 A B t x f s).
Proof. exact (MK_COMB (@lem4011122 B x t) (@lem4011121 A B x f s)). Qed.
Lemma lem4011124 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4011125 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term219 A B t x f s) = (term220 A B t x f s).
Proof. exact (MK_COMB (@lem4011124) (@lem4011123 A B t x f s)). Qed.
Lemma lem4011126 {A B : Type'} (x : B) (f : A -> B) (x' : A) (s : A -> Prop) : (term199 A B x f s x') = (term70 A B x f x' s).
Proof. exact (eq_refl (term199 A B x f s x')). Qed.
Lemma lem4011127 {B : Type'} (x : B) (t : B -> Prop) : (term204 B x t) = (term204 B x t).
Proof. exact (eq_refl (term204 B x t)). Qed.
Lemma lem4011128 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) : (term221 A B t x f s x') = (term222 A B t x f x' s).
Proof. exact (MK_COMB (@lem4011127 B x t) (@lem4011126 A B x f x' s)). Qed.
Lemma lem4011129 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term223 A B t x f s) = (term224 A B t x f s).
Proof. exact (fun_ext (fun x' : A => @lem4011128 A B t x f x' s)). Qed.
Lemma lem4011130 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4011131 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term216 A B t x f s) = (term225 A B t x f s).
Proof. exact (MK_COMB (@lem4011130 A) (@lem4011129 A B t x f s)). Qed.
Lemma lem4011132 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((term215 A B t x f s) = (term216 A B t x f s)) = ((term205 A B t x f s) = (term225 A B t x f s)).
Proof. exact (MK_COMB (@lem4011125 A B t x f s) (@lem4011131 A B t x f s)). Qed.
Lemma lem4011133 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term205 A B t x f s) = (term225 A B t x f s).
Proof. exact (EQ_MP (@lem4011132 A B t x f s) (@lem4011117 A B t x f s)). Qed.
Lemma lem4011134 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term210 A B t x f s) = (term210 A B t x f s).
Proof. exact (eq_refl (term210 A B t x f s)). Qed.
Lemma lem4011135 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term212 A B t x f s) = (term226 A B t x f s).
Proof. exact (MK_COMB (@lem4011134 A B t x f s) (@lem4011133 A B t x f s)). Qed.
Lemma lem4011137 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4011138 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (@lem4011137 A P Q). Qed.
Lemma lem4011139 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term227 A B t x f s) = (term228 A B t x f s).
Proof. exact (@lem4011138 A (term208 A B t x f s) (term224 A B t x f s)). Qed.
Lemma lem4011140 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) : (term229 A B t x f s x') = (term222 A B t x f x' s).
Proof. exact (eq_refl (term229 A B t x f s x')). Qed.
Lemma lem4011141 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term230 A B t x f s) = (term224 A B t x f s).
Proof. exact (fun_ext (fun x' : A => @lem4011140 A B t x f x' s)). Qed.
Lemma lem4011142 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4011143 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term231 A B t x f s) = (term225 A B t x f s).
Proof. exact (MK_COMB (@lem4011142 A) (@lem4011141 A B t x f s)). Qed.
Lemma lem4011144 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term210 A B t x f s) = (term210 A B t x f s).
Proof. exact (eq_refl (term210 A B t x f s)). Qed.
Lemma lem4011145 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term227 A B t x f s) = (term226 A B t x f s).
Proof. exact (MK_COMB (@lem4011144 A B t x f s) (@lem4011143 A B t x f s)). Qed.
Lemma lem4011146 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4011147 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term232 A B t x f s) = (term233 A B t x f s).
Proof. exact (MK_COMB (@lem4011146) (@lem4011145 A B t x f s)). Qed.
Lemma lem4011148 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) : (term229 A B t x f s x') = (term222 A B t x f x' s).
Proof. exact (eq_refl (term229 A B t x f s x')). Qed.
Lemma lem4011149 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term210 A B t x f s) = (term210 A B t x f s).
Proof. exact (eq_refl (term210 A B t x f s)). Qed.
Lemma lem4011150 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) : (term234 A B t x f s x') = (term235 A B t x f x' s).
Proof. exact (MK_COMB (@lem4011149 A B t x f s) (@lem4011148 A B t x f x' s)). Qed.
Lemma lem4011151 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term236 A B t x f s) = (term237 A B t x f s).
Proof. exact (fun_ext (fun x' : A => @lem4011150 A B t x f x' s)). Qed.
Lemma lem4011152 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4011153 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term228 A B t x f s) = (term238 A B t x f s).
Proof. exact (MK_COMB (@lem4011152 A) (@lem4011151 A B t x f s)). Qed.
Lemma lem4011154 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((term227 A B t x f s) = (term228 A B t x f s)) = ((term226 A B t x f s) = (term238 A B t x f s)).
Proof. exact (MK_COMB (@lem4011147 A B t x f s) (@lem4011153 A B t x f s)). Qed.
Lemma lem4011155 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term226 A B t x f s) = (term238 A B t x f s).
Proof. exact (EQ_MP (@lem4011154 A B t x f s) (@lem4011139 A B t x f s)). Qed.
Lemma lem4011157 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term212 A B t x f s) = (term238 A B t x f s).
Proof. exact (TRANS (@lem4011135 A B t x f s) (@lem4011155 A B t x f s)). Qed.
Lemma lem4011158 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term81 A B t x f s) = (term238 A B t x f s).
Proof. exact (TRANS (@lem4011016 A B t x f s) (@lem4011157 A B t x f s)). Qed.
Lemma lem4011159 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term81 A B t x f s) : term238 A B t x f s.
Proof. exact (EQ_MP (@lem4011158 A B t x f s) (@lem4010497 A B t x f s h1)). Qed.
Lemma lem4011160 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term235 A B t x f x' s) : term235 A B t x f x' s.
Proof. exact (h1). Qed.
Lemma lem4011161 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term189 A B t x'' s f.
Proof. exact (h1). Qed.
Lemma lem4011182 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term82 A B s f x t) = (term82 A B s f x t).
Proof. exact (eq_refl (term82 A B s f x t)). Qed.
Lemma lem4011183 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term84 A B s f t) = (term84 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem4011182 A B s f x t)). Qed.
Lemma lem4011184 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011185 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term85 A B s f t) = (term85 A B s f t).
Proof. exact (MK_COMB (@lem4011184 A) (@lem4011183 A B s f t)). Qed.
Lemma lem4011186 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term85 A B s f t.
Proof. exact (EQ_MP (@lem4011185 A B s f t) (@lem4010566 A B s f t h1)). Qed.
Lemma lem4011211 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) : (term222 A B t x f x' s) = (term222 A B t x f x' s).
Proof. exact (eq_refl (term222 A B t x f x' s)). Qed.
Lemma lem4011230 {A B : Type'} (x : B) (f : A -> B) (x' : A) (s : A -> Prop) : (term194 A B x f x' s) = (term194 A B x f x' s).
Proof. exact (eq_refl (term194 A B x f x' s)). Qed.
Lemma lem4011231 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term202 A B x f s) = (term202 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4011230 A B x f x' s)). Qed.
Lemma lem4011232 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011233 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term203 A B x f s) = (term203 A B x f s).
Proof. exact (MK_COMB (@lem4011232 A) (@lem4011231 A B x f s)). Qed.
Lemma lem4011240 {B : Type'} (x : B) (t : B -> Prop) : (term206 B x t) = (term206 B x t).
Proof. exact (eq_refl (term206 B x t)). Qed.
Lemma lem4011241 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term208 A B t x f s) = (term208 A B t x f s).
Proof. exact (MK_COMB (@lem4011240 B x t) (@lem4011233 A B x f s)). Qed.
Lemma lem4011242 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4011243 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term210 A B t x f s) = (term210 A B t x f s).
Proof. exact (MK_COMB (@lem4011242) (@lem4011241 A B t x f s)). Qed.
Lemma lem4011244 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) : (term235 A B t x f x' s) = (term235 A B t x f x' s).
Proof. exact (MK_COMB (@lem4011243 A B t x f s) (@lem4011211 A B t x f x' s)). Qed.
Lemma lem4011245 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term235 A B t x f x' s) : term235 A B t x f x' s.
Proof. exact (EQ_MP (@lem4011244 A B t x f x' s) (@lem4011160 A B t x f x' s h1)). Qed.
Lemma lem4011272 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term95 A B s f y x' x) = (term95 A B s f y x' x).
Proof. exact (eq_refl (term95 A B s f y x' x)). Qed.
Lemma lem4011273 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term121 A B s f y x) = (term121 A B s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4011272 A B s f y x' x)). Qed.
Lemma lem4011274 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011275 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term129 A B s f y x) = (term129 A B s f y x).
Proof. exact (MK_COMB (@lem4011274 A) (@lem4011273 A B s f y x)). Qed.
Lemma lem4011296 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term93 A B s f x y) = (term93 A B s f x y).
Proof. exact (eq_refl (term93 A B s f x y)). Qed.
Lemma lem4011297 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term130 A B s f y x) = (term130 A B s f y x).
Proof. exact (MK_COMB (@lem4011296 A B s f x y) (@lem4011275 A B s f y x)). Qed.
Lemma lem4011298 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term131 A B s f y) = (term131 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4011297 A B s f y x)). Qed.
Lemma lem4011299 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011300 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term132 A B s f y) = (term132 A B s f y).
Proof. exact (MK_COMB (@lem4011299 A) (@lem4011298 A B s f y)). Qed.
Lemma lem4011321 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : B -> A) (y : B) : (term239 A B s f x'' y) = (term239 A B s f x'' y).
Proof. exact (eq_refl (term239 A B s f x'' y)). Qed.
Lemma lem4011322 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term240 A B x'' s f y) = (term240 A B x'' s f y).
Proof. exact (MK_COMB (@lem4011321 A B s f x'' y) (@lem4011300 A B s f y)). Qed.
Lemma lem4011331 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4011332 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term185 A B t x'' s f y) = (term185 A B t x'' s f y).
Proof. exact (MK_COMB (@lem4011331 B y t) (@lem4011322 A B x'' s f y)). Qed.
Lemma lem4011333 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) : (term187 A B t x'' s f) = (term187 A B t x'' s f).
Proof. exact (fun_ext (fun y : B => @lem4011332 A B t x'' s f y)). Qed.
Lemma lem4011334 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4011335 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) : (term189 A B t x'' s f) = (term189 A B t x'' s f).
Proof. exact (MK_COMB (@lem4011334 B) (@lem4011333 A B t x'' s f)). Qed.
Lemma lem4011336 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term189 A B t x'' s f.
Proof. exact (EQ_MP (@lem4011335 A B t x'' s f) (@lem4011161 A B t x'' s f h1)). Qed.
Lemma lem4011337 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term208 A B t x f s) : term208 A B t x f s.
Proof. exact (h1). Qed.
Lemma lem4011338 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term222 A B t x f x' s) : term222 A B t x f x' s.
Proof. exact (h1). Qed.
Lemma lem4011339 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term208 A B t x f s) : term203 A B x f s.
Proof. exact (proj2 (@lem4011337 A B t x f s h1)). Qed.
Lemma lem4011341 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term222 A B t x f x' s) : term70 A B x f x' s.
Proof. exact (proj2 (@lem4011338 A B t x f x' s h1)). Qed.
Lemma lem4011363 {A : Type'} (P : Prop) (Q : A -> Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4011364 {A : Type'} (P : Prop) (Q : A -> Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (@lem4011363 A P Q). Qed.
Lemma lem4011365 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term120 A B s f y x) = (term119 A B s f y x).
Proof. exact (@lem4011364 A (term87 A B s f x y) (term121 A B s f y x)). Qed.
Lemma lem4011366 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term122 A B s f y x x') = (term95 A B s f y x' x).
Proof. exact (eq_refl (term122 A B s f y x x')). Qed.
Lemma lem4011367 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term127 A B s f y x) = (term121 A B s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4011366 A B s f y x' x)). Qed.
Lemma lem4011368 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011369 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term128 A B s f y x) = (term129 A B s f y x).
Proof. exact (MK_COMB (@lem4011368 A) (@lem4011367 A B s f y x)). Qed.
Lemma lem4011370 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term93 A B s f x y) = (term93 A B s f x y).
Proof. exact (eq_refl (term93 A B s f x y)). Qed.
Lemma lem4011371 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term120 A B s f y x) = (term130 A B s f y x).
Proof. exact (MK_COMB (@lem4011370 A B s f x y) (@lem4011369 A B s f y x)). Qed.
Lemma lem4011372 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4011373 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term241 A B s f y x) = (term242 A B s f y x).
Proof. exact (MK_COMB (@lem4011372) (@lem4011371 A B s f y x)). Qed.
Lemma lem4011374 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term122 A B s f y x x') = (term95 A B s f y x' x).
Proof. exact (eq_refl (term122 A B s f y x x')). Qed.
Lemma lem4011375 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term93 A B s f x y) = (term93 A B s f x y).
Proof. exact (eq_refl (term93 A B s f x y)). Qed.
Lemma lem4011376 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term123 A B s f y x x') = (term97 A B s f y x' x).
Proof. exact (MK_COMB (@lem4011375 A B s f x y) (@lem4011374 A B s f y x' x)). Qed.
Lemma lem4011377 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term124 A B s f y x) = (term99 A B s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4011376 A B s f y x' x)). Qed.
Lemma lem4011378 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011379 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term119 A B s f y x) = (term101 A B s f y x).
Proof. exact (MK_COMB (@lem4011378 A) (@lem4011377 A B s f y x)). Qed.
Lemma lem4011380 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : ((term120 A B s f y x) = (term119 A B s f y x)) = ((term130 A B s f y x) = (term101 A B s f y x)).
Proof. exact (MK_COMB (@lem4011373 A B s f y x) (@lem4011379 A B s f y x)). Qed.
Lemma lem4011381 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term130 A B s f y x) = (term101 A B s f y x).
Proof. exact (EQ_MP (@lem4011380 A B s f y x) (@lem4011365 A B s f y x)). Qed.
Lemma lem4011382 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term131 A B s f y) = (term103 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4011381 A B s f y x)). Qed.
Lemma lem4011383 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011384 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term132 A B s f y) = (term105 A B s f y).
Proof. exact (MK_COMB (@lem4011383 A) (@lem4011382 A B s f y)). Qed.
Lemma lem4011385 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : B -> A) (y : B) : (term239 A B s f x'' y) = (term239 A B s f x'' y).
Proof. exact (eq_refl (term239 A B s f x'' y)). Qed.
Lemma lem4011386 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term240 A B x'' s f y) = (term243 A B x'' s f y).
Proof. exact (MK_COMB (@lem4011385 A B s f x'' y) (@lem4011384 A B s f y)). Qed.
Lemma lem4011388 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4011389 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (@lem4011388 A P Q). Qed.
Lemma lem4011390 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term246 A B x'' s f y) = (term247 A B x'' s f y).
Proof. exact (@lem4011389 A (term248 A B s f x'' y) (term103 A B s f y)). Qed.
Lemma lem4011391 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term249 A B s f y x) = (term101 A B s f y x).
Proof. exact (eq_refl (term249 A B s f y x)). Qed.
Lemma lem4011392 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term250 A B s f y) = (term103 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4011391 A B s f y x)). Qed.
Lemma lem4011393 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011394 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term251 A B s f y) = (term105 A B s f y).
Proof. exact (MK_COMB (@lem4011393 A) (@lem4011392 A B s f y)). Qed.
Lemma lem4011395 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : B -> A) (y : B) : (term239 A B s f x'' y) = (term239 A B s f x'' y).
Proof. exact (eq_refl (term239 A B s f x'' y)). Qed.
Lemma lem4011396 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term246 A B x'' s f y) = (term243 A B x'' s f y).
Proof. exact (MK_COMB (@lem4011395 A B s f x'' y) (@lem4011394 A B s f y)). Qed.
Lemma lem4011397 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4011398 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term252 A B x'' s f y) = (term253 A B x'' s f y).
Proof. exact (MK_COMB (@lem4011397) (@lem4011396 A B x'' s f y)). Qed.
Lemma lem4011399 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term249 A B s f y x) = (term101 A B s f y x).
Proof. exact (eq_refl (term249 A B s f y x)). Qed.
Lemma lem4011400 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : B -> A) (y : B) : (term239 A B s f x'' y) = (term239 A B s f x'' y).
Proof. exact (eq_refl (term239 A B s f x'' y)). Qed.
Lemma lem4011401 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term254 A B x'' s f y x) = (term255 A B x'' s f y x).
Proof. exact (MK_COMB (@lem4011400 A B s f x'' y) (@lem4011399 A B s f y x)). Qed.
Lemma lem4011402 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term256 A B x'' s f y) = (term257 A B x'' s f y).
Proof. exact (fun_ext (fun x : A => @lem4011401 A B x'' s f y x)). Qed.
Lemma lem4011403 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011404 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term247 A B x'' s f y) = (term258 A B x'' s f y).
Proof. exact (MK_COMB (@lem4011403 A) (@lem4011402 A B x'' s f y)). Qed.
Lemma lem4011405 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : ((term246 A B x'' s f y) = (term247 A B x'' s f y)) = ((term243 A B x'' s f y) = (term258 A B x'' s f y)).
Proof. exact (MK_COMB (@lem4011398 A B x'' s f y) (@lem4011404 A B x'' s f y)). Qed.
Lemma lem4011406 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term243 A B x'' s f y) = (term258 A B x'' s f y).
Proof. exact (EQ_MP (@lem4011405 A B x'' s f y) (@lem4011390 A B x'' s f y)). Qed.
Lemma lem4011408 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4011409 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (@lem4011408 A P Q). Qed.
Lemma lem4011410 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term259 A B x'' s f y x) = (term260 A B x'' s f y x).
Proof. exact (@lem4011409 A (term248 A B s f x'' y) (term99 A B s f y x)). Qed.
Lemma lem4011411 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term261 A B s f y x x') = (term97 A B s f y x' x).
Proof. exact (eq_refl (term261 A B s f y x x')). Qed.
Lemma lem4011412 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term262 A B s f y x) = (term99 A B s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4011411 A B s f y x' x)). Qed.
Lemma lem4011413 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011414 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term263 A B s f y x) = (term101 A B s f y x).
Proof. exact (MK_COMB (@lem4011413 A) (@lem4011412 A B s f y x)). Qed.
Lemma lem4011415 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : B -> A) (y : B) : (term239 A B s f x'' y) = (term239 A B s f x'' y).
Proof. exact (eq_refl (term239 A B s f x'' y)). Qed.
Lemma lem4011416 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term259 A B x'' s f y x) = (term255 A B x'' s f y x).
Proof. exact (MK_COMB (@lem4011415 A B s f x'' y) (@lem4011414 A B s f y x)). Qed.
Lemma lem4011417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4011418 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term264 A B x'' s f y x) = (term265 A B x'' s f y x).
Proof. exact (MK_COMB (@lem4011417) (@lem4011416 A B x'' s f y x)). Qed.
Lemma lem4011419 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term261 A B s f y x x') = (term97 A B s f y x' x).
Proof. exact (eq_refl (term261 A B s f y x x')). Qed.
Lemma lem4011420 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : B -> A) (y : B) : (term239 A B s f x'' y) = (term239 A B s f x'' y).
Proof. exact (eq_refl (term239 A B s f x'' y)). Qed.
Lemma lem4011421 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term266 A B x'' s f y x x') = (term267 A B x'' s f y x' x).
Proof. exact (MK_COMB (@lem4011420 A B s f x'' y) (@lem4011419 A B s f y x' x)). Qed.
Lemma lem4011422 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term268 A B x'' s f y x) = (term269 A B x'' s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4011421 A B x'' s f y x' x)). Qed.
Lemma lem4011423 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011424 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term260 A B x'' s f y x) = (term270 A B x'' s f y x).
Proof. exact (MK_COMB (@lem4011423 A) (@lem4011422 A B x'' s f y x)). Qed.
Lemma lem4011425 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : ((term259 A B x'' s f y x) = (term260 A B x'' s f y x)) = ((term255 A B x'' s f y x) = (term270 A B x'' s f y x)).
Proof. exact (MK_COMB (@lem4011418 A B x'' s f y x) (@lem4011424 A B x'' s f y x)). Qed.
Lemma lem4011426 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term255 A B x'' s f y x) = (term270 A B x'' s f y x).
Proof. exact (EQ_MP (@lem4011425 A B x'' s f y x) (@lem4011410 A B x'' s f y x)). Qed.
Lemma lem4011427 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term257 A B x'' s f y) = (term271 A B x'' s f y).
Proof. exact (fun_ext (fun x : A => @lem4011426 A B x'' s f y x)). Qed.
Lemma lem4011428 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011429 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term258 A B x'' s f y) = (term272 A B x'' s f y).
Proof. exact (MK_COMB (@lem4011428 A) (@lem4011427 A B x'' s f y)). Qed.
Lemma lem4011430 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term243 A B x'' s f y) = (term272 A B x'' s f y).
Proof. exact (TRANS (@lem4011406 A B x'' s f y) (@lem4011429 A B x'' s f y)). Qed.
Lemma lem4011431 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term240 A B x'' s f y) = (term272 A B x'' s f y).
Proof. exact (TRANS (@lem4011386 A B x'' s f y) (@lem4011430 A B x'' s f y)). Qed.
Lemma lem4011432 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4011433 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term185 A B t x'' s f y) = (term273 A B t x'' s f y).
Proof. exact (MK_COMB (@lem4011432 B y t) (@lem4011431 A B x'' s f y)). Qed.
Lemma lem4011435 {A : Type'} (P : Prop) (Q : A -> Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4011436 {A : Type'} (P : Prop) (Q : A -> Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (@lem4011435 A P Q). Qed.
Lemma lem4011437 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term274 A B t x'' s f y) = (term275 A B t x'' s f y).
Proof. exact (@lem4011436 A (term155 B y t) (term271 A B x'' s f y)). Qed.
Lemma lem4011438 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term276 A B x'' s f y x) = (term270 A B x'' s f y x).
Proof. exact (eq_refl (term276 A B x'' s f y x)). Qed.
Lemma lem4011439 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term277 A B x'' s f y) = (term271 A B x'' s f y).
Proof. exact (fun_ext (fun x : A => @lem4011438 A B x'' s f y x)). Qed.
Lemma lem4011440 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011441 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term278 A B x'' s f y) = (term272 A B x'' s f y).
Proof. exact (MK_COMB (@lem4011440 A) (@lem4011439 A B x'' s f y)). Qed.
Lemma lem4011442 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4011443 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term274 A B t x'' s f y) = (term273 A B t x'' s f y).
Proof. exact (MK_COMB (@lem4011442 B y t) (@lem4011441 A B x'' s f y)). Qed.
Lemma lem4011444 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4011445 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term279 A B t x'' s f y) = (term280 A B t x'' s f y).
Proof. exact (MK_COMB (@lem4011444) (@lem4011443 A B t x'' s f y)). Qed.
Lemma lem4011446 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term276 A B x'' s f y x) = (term270 A B x'' s f y x).
Proof. exact (eq_refl (term276 A B x'' s f y x)). Qed.
Lemma lem4011447 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4011448 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term281 A B t x'' s f y x) = (term282 A B t x'' s f y x).
Proof. exact (MK_COMB (@lem4011447 B y t) (@lem4011446 A B x'' s f y x)). Qed.
Lemma lem4011449 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term283 A B t x'' s f y) = (term284 A B t x'' s f y).
Proof. exact (fun_ext (fun x : A => @lem4011448 A B t x'' s f y x)). Qed.
Lemma lem4011450 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011451 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term275 A B t x'' s f y) = (term285 A B t x'' s f y).
Proof. exact (MK_COMB (@lem4011450 A) (@lem4011449 A B t x'' s f y)). Qed.
Lemma lem4011452 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : ((term274 A B t x'' s f y) = (term275 A B t x'' s f y)) = ((term273 A B t x'' s f y) = (term285 A B t x'' s f y)).
Proof. exact (MK_COMB (@lem4011445 A B t x'' s f y) (@lem4011451 A B t x'' s f y)). Qed.
Lemma lem4011453 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term273 A B t x'' s f y) = (term285 A B t x'' s f y).
Proof. exact (EQ_MP (@lem4011452 A B t x'' s f y) (@lem4011437 A B t x'' s f y)). Qed.
Lemma lem4011455 {A : Type'} (P : Prop) (Q : A -> Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4011456 {A : Type'} (P : Prop) (Q : A -> Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (@lem4011455 A P Q). Qed.
Lemma lem4011457 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term286 A B t x'' s f y x) = (term287 A B t x'' s f y x).
Proof. exact (@lem4011456 A (term155 B y t) (term269 A B x'' s f y x)). Qed.
Lemma lem4011458 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term288 A B x'' s f y x x') = (term267 A B x'' s f y x' x).
Proof. exact (eq_refl (term288 A B x'' s f y x x')). Qed.
Lemma lem4011459 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term289 A B x'' s f y x) = (term269 A B x'' s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4011458 A B x'' s f y x' x)). Qed.
Lemma lem4011460 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011461 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term290 A B x'' s f y x) = (term270 A B x'' s f y x).
Proof. exact (MK_COMB (@lem4011460 A) (@lem4011459 A B x'' s f y x)). Qed.
Lemma lem4011462 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4011463 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term286 A B t x'' s f y x) = (term282 A B t x'' s f y x).
Proof. exact (MK_COMB (@lem4011462 B y t) (@lem4011461 A B x'' s f y x)). Qed.
Lemma lem4011464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4011465 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term291 A B t x'' s f y x) = (term292 A B t x'' s f y x).
Proof. exact (MK_COMB (@lem4011464) (@lem4011463 A B t x'' s f y x)). Qed.
Lemma lem4011466 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term288 A B x'' s f y x x') = (term267 A B x'' s f y x' x).
Proof. exact (eq_refl (term288 A B x'' s f y x x')). Qed.
Lemma lem4011467 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4011468 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term293 A B t x'' s f y x x') = (term294 A B t x'' s f y x' x).
Proof. exact (MK_COMB (@lem4011467 B y t) (@lem4011466 A B x'' s f y x' x)). Qed.
Lemma lem4011469 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term295 A B t x'' s f y x) = (term296 A B t x'' s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4011468 A B t x'' s f y x' x)). Qed.
Lemma lem4011470 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011471 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term287 A B t x'' s f y x) = (term297 A B t x'' s f y x).
Proof. exact (MK_COMB (@lem4011470 A) (@lem4011469 A B t x'' s f y x)). Qed.
Lemma lem4011472 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : ((term286 A B t x'' s f y x) = (term287 A B t x'' s f y x)) = ((term282 A B t x'' s f y x) = (term297 A B t x'' s f y x)).
Proof. exact (MK_COMB (@lem4011465 A B t x'' s f y x) (@lem4011471 A B t x'' s f y x)). Qed.
Lemma lem4011473 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term282 A B t x'' s f y x) = (term297 A B t x'' s f y x).
Proof. exact (EQ_MP (@lem4011472 A B t x'' s f y x) (@lem4011457 A B t x'' s f y x)). Qed.
Lemma lem4011474 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term284 A B t x'' s f y) = (term298 A B t x'' s f y).
Proof. exact (fun_ext (fun x : A => @lem4011473 A B t x'' s f y x)). Qed.
Lemma lem4011475 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011476 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term285 A B t x'' s f y) = (term299 A B t x'' s f y).
Proof. exact (MK_COMB (@lem4011475 A) (@lem4011474 A B t x'' s f y)). Qed.
Lemma lem4011477 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term273 A B t x'' s f y) = (term299 A B t x'' s f y).
Proof. exact (TRANS (@lem4011453 A B t x'' s f y) (@lem4011476 A B t x'' s f y)). Qed.
Lemma lem4011478 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term185 A B t x'' s f y) = (term299 A B t x'' s f y).
Proof. exact (TRANS (@lem4011433 A B t x'' s f y) (@lem4011477 A B t x'' s f y)). Qed.
Lemma lem4011479 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) : (term187 A B t x'' s f) = (term300 A B t x'' s f).
Proof. exact (fun_ext (fun y : B => @lem4011478 A B t x'' s f y)). Qed.
Lemma lem4011480 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4011481 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) : (term189 A B t x'' s f) = (term301 A B t x'' s f).
Proof. exact (MK_COMB (@lem4011480 B) (@lem4011479 A B t x'' s f)). Qed.
Lemma lem4011519 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term294 A B t x'' s f y x' x) = (term302 A B x'' t s f y x' x).
Proof. exact (@lem19490 (term248 A B s f x'' y) (term155 B y t) (term97 A B s f y x' x)). Qed.
Lemma lem4011520 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term303 A B t s f y x' x) = (term303 A B t s f y x' x).
Proof. exact (eq_refl (term303 A B t s f y x' x)). Qed.
Lemma lem4011527 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x'' : B -> A) (y : B) : (term304 A B t s f x'' y) = (term305 A B s t f x'' y).
Proof. exact (@lem19490 (term306 A B x'' y s) (term155 B y t) ((term307 A B f x'' y) = y)). Qed.
Lemma lem4011528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4011529 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x'' : B -> A) (y : B) : (term308 A B t s f x'' y) = (term309 A B s t f x'' y).
Proof. exact (MK_COMB (@lem4011528) (@lem4011527 A B s t f x'' y)). Qed.
Lemma lem4011530 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term302 A B x'' t s f y x' x) = (term310 A B x'' t s f y x' x).
Proof. exact (MK_COMB (@lem4011529 A B s t f x'' y) (@lem4011520 A B t s f y x' x)). Qed.
Lemma lem4011532 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term294 A B t x'' s f y x' x) = (term310 A B x'' t s f y x' x).
Proof. exact (TRANS (@lem4011519 A B x'' t s f y x' x) (@lem4011530 A B x'' t s f y x' x)). Qed.
Lemma lem4011533 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term296 A B t x'' s f y x) = (term311 A B x'' t s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4011532 A B x'' t s f y x' x)). Qed.
Lemma lem4011534 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011535 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term297 A B t x'' s f y x) = (term312 A B x'' t s f y x).
Proof. exact (MK_COMB (@lem4011534 A) (@lem4011533 A B x'' t s f y x)). Qed.
Lemma lem4011536 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term298 A B t x'' s f y) = (term313 A B x'' t s f y).
Proof. exact (fun_ext (fun x : A => @lem4011535 A B x'' t s f y x)). Qed.
Lemma lem4011537 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011538 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term299 A B t x'' s f y) = (term314 A B x'' t s f y).
Proof. exact (MK_COMB (@lem4011537 A) (@lem4011536 A B x'' t s f y)). Qed.
Lemma lem4011539 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term300 A B t x'' s f) = (term315 A B x'' t s f).
Proof. exact (fun_ext (fun y : B => @lem4011538 A B x'' t s f y)). Qed.
Lemma lem4011540 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4011541 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term301 A B t x'' s f) = (term316 A B x'' t s f).
Proof. exact (MK_COMB (@lem4011540 B) (@lem4011539 A B x'' t s f)). Qed.
Lemma lem4011542 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term189 A B t x'' s f) = (term316 A B x'' t s f).
Proof. exact (TRANS (@lem4011481 A B t x'' s f) (@lem4011541 A B x'' t s f)). Qed.
Lemma lem4011543 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term316 A B x'' t s f.
Proof. exact (EQ_MP (@lem4011542 A B x'' t s f) (@lem4011336 A B t x'' s f h1)). Qed.
Lemma lem4011555 {A B : Type'} (x : B) (f : A -> B) (x' : A) (s : A -> Prop) : (term194 A B x f x' s) = (term194 A B x f x' s).
Proof. exact (eq_refl (term194 A B x f x' s)). Qed.
Lemma lem4011556 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term202 A B x f s) = (term202 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4011555 A B x f x' s)). Qed.
Lemma lem4011557 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011559 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term203 A B x f s) = (term203 A B x f s).
Proof. exact (MK_COMB (@lem4011557 A) (@lem4011556 A B x f s)). Qed.
Lemma lem4011560 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term208 A B t x f s) : term203 A B x f s.
Proof. exact (EQ_MP (@lem4011559 A B x f s) (@lem4011339 A B t x f s h1)). Qed.
Lemma lem4011572 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term82 A B s f x t) = (term82 A B s f x t).
Proof. exact (eq_refl (term82 A B s f x t)). Qed.
Lemma lem4011573 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term84 A B s f t) = (term84 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem4011572 A B s f x t)). Qed.
Lemma lem4011574 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4011576 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term85 A B s f t) = (term85 A B s f t).
Proof. exact (MK_COMB (@lem4011574 A) (@lem4011573 A B s f t)). Qed.
Lemma lem4011577 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term85 A B s f t.
Proof. exact (EQ_MP (@lem4011576 A B s f t) (@lem4011186 A B s f t h1)). Qed.
Lemma lem4011775 {A B : Type'} (_46303 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term317 A B x'' t s f _46303.
Proof. exact (@lem4011543 A B t x'' s f h1 _46303). Qed.
Lemma lem4011776 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (_46303 : B) : (term317 A B x'' t s f _46303) = (term314 A B x'' t s f _46303).
Proof. exact (eq_refl (term317 A B x'' t s f _46303)). Qed.
Lemma lem4011777 {A B : Type'} (_46303 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term314 A B x'' t s f _46303.
Proof. exact (EQ_MP (@lem4011776 A B x'' t s f _46303) (@lem4011775 A B _46303 t x'' s f h1)). Qed.
Lemma lem4011778 {A B : Type'} (_46303 : B) (_46304 : A) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term318 A B x'' t s f _46303 _46304.
Proof. exact (@lem4011777 A B _46303 t x'' s f h1 _46304). Qed.
Lemma lem4011779 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (_46303 : B) (_46304 : A) : (term318 A B x'' t s f _46303 _46304) = (term312 A B x'' t s f _46303 _46304).
Proof. exact (eq_refl (term318 A B x'' t s f _46303 _46304)). Qed.
Lemma lem4011780 {A B : Type'} (_46303 : B) (_46304 : A) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term312 A B x'' t s f _46303 _46304.
Proof. exact (EQ_MP (@lem4011779 A B x'' t s f _46303 _46304) (@lem4011778 A B _46303 _46304 t x'' s f h1)). Qed.
Lemma lem4011781 {A B : Type'} (_46303 : B) (_46304 : A) (_46305 : A) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term319 A B x'' t s f _46303 _46304 _46305.
Proof. exact (@lem4011780 A B _46303 _46304 t x'' s f h1 _46305). Qed.
Lemma lem4011782 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (_46303 : B) (_46305 : A) (_46304 : A) : (term319 A B x'' t s f _46303 _46304 _46305) = (term310 A B x'' t s f _46303 _46305 _46304).
Proof. exact (eq_refl (term319 A B x'' t s f _46303 _46304 _46305)). Qed.
Lemma lem4011783 {A B : Type'} (_46303 : B) (_46305 : A) (_46304 : A) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term310 A B x'' t s f _46303 _46305 _46304.
Proof. exact (EQ_MP (@lem4011782 A B x'' t s f _46303 _46305 _46304) (@lem4011781 A B _46303 _46304 _46305 t x'' s f h1)). Qed.
Lemma lem4011784 {A B : Type'} (_46306 : A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term208 A B t x f s) : term320 A B x f s _46306.
Proof. exact (@lem4011560 A B t x f s h1 _46306). Qed.
Lemma lem4011785 {A B : Type'} (x : B) (f : A -> B) (_46306 : A) (s : A -> Prop) : (term320 A B x f s _46306) = (term194 A B x f _46306 s).
Proof. exact (eq_refl (term320 A B x f s _46306)). Qed.
Lemma lem4011787 {A B : Type'} (_46307 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term321 A B s f t _46307.
Proof. exact (@lem4011577 A B s f t h1 _46307). Qed.
Lemma lem4011788 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46307 : A) (t : B -> Prop) : (term321 A B s f t _46307) = (term82 A B s f _46307 t).
Proof. exact (eq_refl (term321 A B s f t _46307)). Qed.
Lemma lem4011800 {A B : Type'} (_46303 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term305 A B s t f x'' _46303.
Proof. exact (proj1 (@lem4011783 A B _46303 (@el A) (@el A) t x'' s f h1)). Qed.
Lemma lem4011822 {A B : Type'} (_46306 : A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term208 A B t x f s) : term194 A B x f _46306 s.
Proof. exact (EQ_MP (@lem4011785 A B x f _46306 s) (@lem4011784 A B _46306 t x f s h1)). Qed.
Lemma lem4011854 {A B : Type'} (_46303 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term322 A B t x'' _46303 s.
Proof. exact (proj1 (@lem4011800 A B _46303 t x'' s f h1)). Qed.
Lemma lem4011860 {A B : Type'} (_46303 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term323 A B t f x'' _46303.
Proof. exact (proj2 (@lem4011800 A B _46303 t x'' s f h1)). Qed.
Lemma lem4011870 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term222 A B t x f x' s) : term155 B x t.
Proof. exact (proj1 (@lem4011338 A B t x f x' s h1)). Qed.
Lemma lem4011872 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term222 A B t x f x' s) : x = (f x').
Proof. exact (proj1 (@lem4011341 A B t x f x' s h1)). Qed.
Lemma lem4011954 {A B : Type'} (_46307 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term82 A B s f _46307 t.
Proof. exact (EQ_MP (@lem4011788 A B s f _46307 t) (@lem4011787 A B _46307 s f t h1)). Qed.
Lemma lem4011955 {B : Type'} (t : B -> Prop) : (term324 B t) = (term324 B t).
Proof. exact (eq_refl (term324 B t)). Qed.
Lemma lem4011956 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term222 A B t x f x' s) : (term325 B t x) = (term326 A B t f x').
Proof. exact (MK_COMB (@lem4011955 B t) (@lem4011872 A B t x f x' s h1)). Qed.
Lemma lem4011957 {A B : Type'} (f : A -> B) (x' : A) (t : B -> Prop) : (term326 A B t f x') = (term327 A B f x' t).
Proof. exact (eq_refl (term326 A B t f x')). Qed.
Lemma lem4011958 {B : Type'} (t : B -> Prop) (x : B) : (term328 B t x) = (term328 B t x).
Proof. exact (eq_refl (term328 B t x)). Qed.
Lemma lem4011959 {A B : Type'} (x : B) (f : A -> B) (x' : A) (t : B -> Prop) : ((term325 B t x) = (term326 A B t f x')) = ((term325 B t x) = (term327 A B f x' t)).
Proof. exact (MK_COMB (@lem4011958 B t x) (@lem4011957 A B f x' t)). Qed.
Lemma lem4011960 {B : Type'} (x : B) (t : B -> Prop) : (term325 B t x) = (term155 B x t).
Proof. exact (eq_refl (term325 B t x)). Qed.
Lemma lem4011961 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4011962 {B : Type'} (x : B) (t : B -> Prop) : (term328 B t x) = (term329 B x t).
Proof. exact (MK_COMB (@lem4011961) (@lem4011960 B x t)). Qed.
Lemma lem4011963 {A B : Type'} (f : A -> B) (x' : A) (t : B -> Prop) : (term327 A B f x' t) = (term327 A B f x' t).
Proof. exact (eq_refl (term327 A B f x' t)). Qed.
Lemma lem4011964 {A B : Type'} (x : B) (f : A -> B) (x' : A) (t : B -> Prop) : ((term325 B t x) = (term327 A B f x' t)) = ((term155 B x t) = (term327 A B f x' t)).
Proof. exact (MK_COMB (@lem4011962 B x t) (@lem4011963 A B f x' t)). Qed.
Lemma lem4011965 {A B : Type'} (x : B) (f : A -> B) (x' : A) (t : B -> Prop) : ((term325 B t x) = (term326 A B t f x')) = ((term155 B x t) = (term327 A B f x' t)).
Proof. exact (TRANS (@lem4011959 A B x f x' t) (@lem4011964 A B x f x' t)). Qed.
Lemma lem4011966 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term222 A B t x f x' s) : (term155 B x t) = (term327 A B f x' t).
Proof. exact (EQ_MP (@lem4011965 A B x f x' t) (@lem4011956 A B t x f x' s h1)). Qed.
Lemma lem4011967 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term222 A B t x f x' s) : term327 A B f x' t.
Proof. exact (EQ_MP (@lem4011966 A B t x f x' s h1) (@lem4011870 A B t x f x' s h1)). Qed.
Lemma lem4012091 {B : Type'} (x : B) (y : B) (z : B) : term330 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem4012099 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term208 A B t x f s) : @IN B x t.
Proof. exact (proj1 (@lem4011337 A B t x f s h1)). Qed.
Lemma lem4012100 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term208 A B t x f s) : term331 B x t.
Proof. exact (fun h0 : term155 B x t => @lem4012099 A B t x f s h1). Qed.
Lemma lem4012102 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4012103 {B : Type'} (x : B) (t : B -> Prop) : (term331 B x t) = (@IN B x t).
Proof. exact (@lem4012102 (@IN B x t)). Qed.
Lemma lem4012104 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term208 A B t x f s) : @IN B x t.
Proof. exact (EQ_MP (@lem4012103 B x t) (@lem4012100 A B t x f s h1)). Qed.
Lemma lem4012110 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4012111 {A B : Type'} (f : A -> B) (x'' : B -> A) (_46303 : B) (t : B -> Prop) : (term323 A B t f x'' _46303) = (term333 A B f x'' _46303 t).
Proof. exact (@lem4012110 ((term307 A B f x'' _46303) = _46303) (term155 B _46303 t)). Qed.
Lemma lem4012119 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4012120 {A B : Type'} (f : A -> B) (x'' : B -> A) (_46303 : B) (t : B -> Prop) : (term334 A B t f x'' _46303) = (term335 A B f x'' _46303 t).
Proof. exact (MK_COMB (@lem4012119) (@lem4012111 A B f x'' _46303 t)). Qed.
Lemma lem4012128 {A B : Type'} (f : A -> B) (x'' : B -> A) (_46303 : B) (t : B -> Prop) : (term333 A B f x'' _46303 t) = (term333 A B f x'' _46303 t).
Proof. exact (eq_refl (term333 A B f x'' _46303 t)). Qed.
Lemma lem4012129 {A B : Type'} (f : A -> B) (x'' : B -> A) (_46303 : B) (t : B -> Prop) : ((term323 A B t f x'' _46303) = (term333 A B f x'' _46303 t)) = ((term333 A B f x'' _46303 t) = (term333 A B f x'' _46303 t)).
Proof. exact (MK_COMB (@lem4012120 A B f x'' _46303 t) (@lem4012128 A B f x'' _46303 t)). Qed.
Lemma lem4012131 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4012132 (x : Prop) : (x = x) = True.
Proof. exact (@lem4012131 Prop x). Qed.
Lemma lem4012133 {A B : Type'} (f : A -> B) (x'' : B -> A) (_46303 : B) (t : B -> Prop) : ((term333 A B f x'' _46303 t) = (term333 A B f x'' _46303 t)) = True.
Proof. exact (@lem4012132 (term333 A B f x'' _46303 t)). Qed.
Lemma lem4012134 {A B : Type'} (f : A -> B) (x'' : B -> A) (_46303 : B) (t : B -> Prop) : ((term323 A B t f x'' _46303) = (term333 A B f x'' _46303 t)) = True.
Proof. exact (TRANS (@lem4012129 A B f x'' _46303 t) (@lem4012133 A B f x'' _46303 t)). Qed.
Lemma lem4012135 {A B : Type'} (f : A -> B) (x'' : B -> A) (_46303 : B) (t : B -> Prop) : True = ((term323 A B t f x'' _46303) = (term333 A B f x'' _46303 t)).
Proof. exact (SYM (@lem4012134 A B f x'' _46303 t)). Qed.
Lemma lem4012136 {A B : Type'} (f : A -> B) (x'' : B -> A) (_46303 : B) (t : B -> Prop) : (term323 A B t f x'' _46303) = (term333 A B f x'' _46303 t).
Proof. exact (EQ_MP (@lem4012135 A B f x'' _46303 t) (@lem0)). Qed.
Lemma lem4012137 {A B : Type'} (_46303 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term333 A B f x'' _46303 t.
Proof. exact (EQ_MP (@lem4012136 A B f x'' _46303 t) (@lem4011860 A B _46303 t x'' s f h1)). Qed.
Lemma lem4012139 (b : Prop) (a : Prop) : (a \/ b) = (term336 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4012140 {A B : Type'} (t : B -> Prop) (f : A -> B) (x'' : B -> A) (_46303 : B) : (term333 A B f x'' _46303 t) = (term337 A B t f x'' _46303).
Proof. exact (@lem4012139 (term155 B _46303 t) ((term307 A B f x'' _46303) = _46303)). Qed.
Lemma lem4012142 (a : Prop) : (term49 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4012143 {B : Type'} (_46303 : B) (t : B -> Prop) : (term338 B _46303 t) = (@IN B _46303 t).
Proof. exact (@lem4012142 (@IN B _46303 t)). Qed.
Lemma lem4012144 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4012145 {B : Type'} (_46303 : B) (t : B -> Prop) : (term339 B _46303 t) = (term75 B _46303 t).
Proof. exact (MK_COMB (@lem4012144) (@lem4012143 B _46303 t)). Qed.
Lemma lem4012146 {A B : Type'} (f : A -> B) (x'' : B -> A) (_46303 : B) : ((term307 A B f x'' _46303) = _46303) = ((term307 A B f x'' _46303) = _46303).
Proof. exact (eq_refl ((term307 A B f x'' _46303) = _46303)). Qed.
Lemma lem4012147 {A B : Type'} (t : B -> Prop) (f : A -> B) (x'' : B -> A) (_46303 : B) : (term337 A B t f x'' _46303) = (term340 A B t f x'' _46303).
Proof. exact (MK_COMB (@lem4012145 B _46303 t) (@lem4012146 A B f x'' _46303)). Qed.
Lemma lem4012148 {A B : Type'} (t : B -> Prop) (f : A -> B) (x'' : B -> A) (_46303 : B) : (term333 A B f x'' _46303 t) = (term340 A B t f x'' _46303).
Proof. exact (TRANS (@lem4012140 A B t f x'' _46303) (@lem4012147 A B t f x'' _46303)). Qed.
Lemma lem4012151 {A B : Type'} (_46303 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term340 A B t f x'' _46303.
Proof. exact (EQ_MP (@lem4012148 A B t f x'' _46303) (@lem4012137 A B _46303 t x'' s f h1)). Qed.
Lemma lem4012152 {A B : Type'} (_46303 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term340 A B t f x'' _46303.
Proof. exact (@lem4012151 A B _46303 t x'' s f h1). Qed.
Lemma lem4012153 {A B : Type'} (x : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term340 A B t f x'' x.
Proof. exact (@lem4012152 A B x t x'' s f h1). Qed.
Lemma lem4012156 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term189 A B t x'' s f) (h2 : term208 A B t x f s) : (term307 A B f x'' x) = x.
Proof. exact (@lem4012153 A B x t x'' s f h1 (@lem4012104 A B t x f s h2)). Qed.
Lemma lem4012157 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term189 A B t x'' s f) (h2 : term208 A B t x f s) : term341 A B f x'' x.
Proof. exact (fun h0 : term342 A B f x'' x => @lem4012156 A B x'' t x f s h1 h2). Qed.
Lemma lem4012159 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4012160 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term341 A B f x'' x) = ((term307 A B f x'' x) = x).
Proof. exact (@lem4012159 ((term307 A B f x'' x) = x)). Qed.
Lemma lem4012161 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term189 A B t x'' s f) (h2 : term208 A B t x f s) : (term307 A B f x'' x) = x.
Proof. exact (EQ_MP (@lem4012160 A B f x'' x) (@lem4012157 A B x'' t x f s h1 h2)). Qed.
Lemma lem4012163 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4012164 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4012163 B x). Qed.
Lemma lem4012165 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term307 A B f x'' x) = (term307 A B f x'' x).
Proof. exact (@lem4012164 B (term307 A B f x'' x)). Qed.
Lemma lem4012166 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : term343 A B f x'' x.
Proof. exact (fun h0 : term344 A B f x'' x => @lem4012165 A B f x'' x). Qed.
Lemma lem4012168 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4012169 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term343 A B f x'' x) = ((term307 A B f x'' x) = (term307 A B f x'' x)).
Proof. exact (@lem4012168 ((term307 A B f x'' x) = (term307 A B f x'' x))). Qed.
Lemma lem4012170 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term307 A B f x'' x) = (term307 A B f x'' x).
Proof. exact (EQ_MP (@lem4012169 A B f x'' x) (@lem4012166 A B f x'' x)). Qed.
Lemma lem4012188 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4012189 {B : Type'} (y : B) (x : B) (z : B) : (term345 B x y z) = (term346 B y x z).
Proof. exact (@lem4012188 (y = z) (term347 B x z)). Qed.
Lemma lem4012199 {B : Type'} (x : B) (y : B) : (term348 B x y) = (term348 B x y).
Proof. exact (eq_refl (term348 B x y)). Qed.
Lemma lem4012200 {B : Type'} (y : B) (x : B) (z : B) : (term330 B x y z) = (term349 B y x z).
Proof. exact (MK_COMB (@lem4012199 B x y) (@lem4012189 B y x z)). Qed.
Lemma lem4012204 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4012205 {B : Type'} (y : B) (x : B) (z : B) : (term349 B y x z) = (term350 B y x z).
Proof. exact (@lem4012204 (y = z) (term347 B x y) (term347 B x z)). Qed.
Lemma lem4012227 {B : Type'} (y : B) (x : B) (z : B) : (term330 B x y z) = (term350 B y x z).
Proof. exact (TRANS (@lem4012200 B y x z) (@lem4012205 B y x z)). Qed.
Lemma lem4012228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4012229 {B : Type'} (y : B) (x : B) (z : B) : (term351 B x y z) = (term352 B y x z).
Proof. exact (MK_COMB (@lem4012228) (@lem4012227 B y x z)). Qed.
Lemma lem4012251 {B : Type'} (y : B) (x : B) (z : B) : (term350 B y x z) = (term350 B y x z).
Proof. exact (eq_refl (term350 B y x z)). Qed.
Lemma lem4012252 {B : Type'} (y : B) (x : B) (z : B) : ((term330 B x y z) = (term350 B y x z)) = ((term350 B y x z) = (term350 B y x z)).
Proof. exact (MK_COMB (@lem4012229 B y x z) (@lem4012251 B y x z)). Qed.
Lemma lem4012254 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4012255 (x : Prop) : (x = x) = True.
Proof. exact (@lem4012254 Prop x). Qed.
Lemma lem4012256 {B : Type'} (y : B) (x : B) (z : B) : ((term350 B y x z) = (term350 B y x z)) = True.
Proof. exact (@lem4012255 (term350 B y x z)). Qed.
Lemma lem4012257 {B : Type'} (y : B) (x : B) (z : B) : ((term330 B x y z) = (term350 B y x z)) = True.
Proof. exact (TRANS (@lem4012252 B y x z) (@lem4012256 B y x z)). Qed.
Lemma lem4012258 {B : Type'} (y : B) (x : B) (z : B) : True = ((term330 B x y z) = (term350 B y x z)).
Proof. exact (SYM (@lem4012257 B y x z)). Qed.
Lemma lem4012259 {B : Type'} (y : B) (x : B) (z : B) : (term330 B x y z) = (term350 B y x z).
Proof. exact (EQ_MP (@lem4012258 B y x z) (@lem0)). Qed.
Lemma lem4012260 {B : Type'} (y : B) (x : B) (z : B) : term350 B y x z.
Proof. exact (EQ_MP (@lem4012259 B y x z) (@lem4012091 B x y z)). Qed.
Lemma lem4012262 (b : Prop) (a : Prop) : (a \/ b) = (term336 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4012263 {B : Type'} (x : B) (y : B) (z : B) : (term350 B y x z) = (term353 B x y z).
Proof. exact (@lem4012262 (term354 B y x z) (y = z)). Qed.
Lemma lem4012265 (a : Prop) (b : Prop) : (term355 a b) = (term356 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4012266 {B : Type'} (y : B) (x : B) (z : B) : (term357 B y x z) = (term358 B y x z).
Proof. exact (@lem4012265 (term347 B x y) (term347 B x z)). Qed.
Lemma lem4012268 (a : Prop) : (term49 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4012269 {B : Type'} (x : B) (y : B) : (term359 B x y) = (x = y).
Proof. exact (@lem4012268 (x = y)). Qed.
Lemma lem4012270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4012271 {B : Type'} (x : B) (y : B) : (term360 B x y) = (term361 B x y).
Proof. exact (MK_COMB (@lem4012270) (@lem4012269 B x y)). Qed.
Lemma lem4012273 (a : Prop) : (term49 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4012274 {B : Type'} (x : B) (z : B) : (term359 B x z) = (x = z).
Proof. exact (@lem4012273 (x = z)). Qed.
Lemma lem4012275 {B : Type'} (y : B) (x : B) (z : B) : (term358 B y x z) = (term362 B y x z).
Proof. exact (MK_COMB (@lem4012271 B x y) (@lem4012274 B x z)). Qed.
Lemma lem4012276 {B : Type'} (y : B) (x : B) (z : B) : (term357 B y x z) = (term362 B y x z).
Proof. exact (TRANS (@lem4012266 B y x z) (@lem4012275 B y x z)). Qed.
Lemma lem4012277 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4012278 {B : Type'} (y : B) (x : B) (z : B) : (term363 B y x z) = (term364 B y x z).
Proof. exact (MK_COMB (@lem4012277) (@lem4012276 B y x z)). Qed.
Lemma lem4012279 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4012280 {B : Type'} (x : B) (y : B) (z : B) : (term353 B x y z) = (term365 B x y z).
Proof. exact (MK_COMB (@lem4012278 B y x z) (@lem4012279 B y z)). Qed.
Lemma lem4012281 {B : Type'} (x : B) (y : B) (z : B) : (term350 B y x z) = (term365 B x y z).
Proof. exact (TRANS (@lem4012263 B x y z) (@lem4012280 B x y z)). Qed.
Lemma lem4012283 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term189 A B t x'' s f) (h2 : term208 A B t x f s) : term366 A B f x'' x.
Proof. exact (conj (@lem4012161 A B x'' t x f s h1 h2) (@lem4012170 A B f x'' x)). Qed.
Lemma lem4012285 {B : Type'} (x : B) (y : B) (z : B) : term365 B x y z.
Proof. exact (EQ_MP (@lem4012281 B x y z) (@lem4012260 B y x z)). Qed.
Lemma lem4012286 {B : Type'} (x : B) (y : B) (z : B) : term365 B x y z.
Proof. exact (@lem4012285 B x y z). Qed.
Lemma lem4012287 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : term367 A B f x'' x.
Proof. exact (@lem4012286 B (term307 A B f x'' x) x (term307 A B f x'' x)). Qed.
Lemma lem4012290 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term189 A B t x'' s f) (h2 : term208 A B t x f s) : x = (term307 A B f x'' x).
Proof. exact (@lem4012287 A B f x'' x (@lem4012283 A B x'' t x f s h1 h2)). Qed.
Lemma lem4012291 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term189 A B t x'' s f) (h2 : term208 A B t x f s) : term368 A B f x'' x.
Proof. exact (fun h0 : term369 A B f x'' x => @lem4012290 A B x'' t x f s h1 h2). Qed.
Lemma lem4012293 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4012294 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term368 A B f x'' x) = (x = (term307 A B f x'' x)).
Proof. exact (@lem4012293 (x = (term307 A B f x'' x))). Qed.
Lemma lem4012295 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term189 A B t x'' s f) (h2 : term208 A B t x f s) : x = (term307 A B f x'' x).
Proof. exact (EQ_MP (@lem4012294 A B f x'' x) (@lem4012291 A B x'' t x f s h1 h2)). Qed.
Lemma lem4012297 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term208 A B t x f s) : @IN B x t.
Proof. exact (proj1 (@lem4011337 A B t x f s h1)). Qed.
Lemma lem4012298 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term208 A B t x f s) : term331 B x t.
Proof. exact (fun h0 : term155 B x t => @lem4012297 A B t x f s h1). Qed.
Lemma lem4012300 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4012301 {B : Type'} (x : B) (t : B -> Prop) : (term331 B x t) = (@IN B x t).
Proof. exact (@lem4012300 (@IN B x t)). Qed.
Lemma lem4012302 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term208 A B t x f s) : @IN B x t.
Proof. exact (EQ_MP (@lem4012301 B x t) (@lem4012298 A B t x f s h1)). Qed.
Lemma lem4012308 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4012309 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_46303 : B) (t : B -> Prop) : (term322 A B t x'' _46303 s) = (term370 A B x'' s _46303 t).
Proof. exact (@lem4012308 (term306 A B x'' _46303 s) (term155 B _46303 t)). Qed.
Lemma lem4012315 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4012316 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_46303 : B) (t : B -> Prop) : (term371 A B t x'' _46303 s) = (term372 A B x'' s _46303 t).
Proof. exact (MK_COMB (@lem4012315) (@lem4012309 A B x'' s _46303 t)). Qed.
Lemma lem4012322 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_46303 : B) (t : B -> Prop) : (term370 A B x'' s _46303 t) = (term370 A B x'' s _46303 t).
Proof. exact (eq_refl (term370 A B x'' s _46303 t)). Qed.
Lemma lem4012323 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_46303 : B) (t : B -> Prop) : ((term322 A B t x'' _46303 s) = (term370 A B x'' s _46303 t)) = ((term370 A B x'' s _46303 t) = (term370 A B x'' s _46303 t)).
Proof. exact (MK_COMB (@lem4012316 A B x'' s _46303 t) (@lem4012322 A B x'' s _46303 t)). Qed.
Lemma lem4012325 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4012326 (x : Prop) : (x = x) = True.
Proof. exact (@lem4012325 Prop x). Qed.
Lemma lem4012327 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_46303 : B) (t : B -> Prop) : ((term370 A B x'' s _46303 t) = (term370 A B x'' s _46303 t)) = True.
Proof. exact (@lem4012326 (term370 A B x'' s _46303 t)). Qed.
Lemma lem4012328 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_46303 : B) (t : B -> Prop) : ((term322 A B t x'' _46303 s) = (term370 A B x'' s _46303 t)) = True.
Proof. exact (TRANS (@lem4012323 A B x'' s _46303 t) (@lem4012327 A B x'' s _46303 t)). Qed.
Lemma lem4012329 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_46303 : B) (t : B -> Prop) : True = ((term322 A B t x'' _46303 s) = (term370 A B x'' s _46303 t)).
Proof. exact (SYM (@lem4012328 A B x'' s _46303 t)). Qed.
Lemma lem4012330 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_46303 : B) (t : B -> Prop) : (term322 A B t x'' _46303 s) = (term370 A B x'' s _46303 t).
Proof. exact (EQ_MP (@lem4012329 A B x'' s _46303 t) (@lem0)). Qed.
Lemma lem4012331 {A B : Type'} (_46303 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term370 A B x'' s _46303 t.
Proof. exact (EQ_MP (@lem4012330 A B x'' s _46303 t) (@lem4011854 A B _46303 t x'' s f h1)). Qed.
Lemma lem4012333 (b : Prop) (a : Prop) : (a \/ b) = (term336 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4012334 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (_46303 : B) (s : A -> Prop) : (term370 A B x'' s _46303 t) = (term373 A B t x'' _46303 s).
Proof. exact (@lem4012333 (term155 B _46303 t) (term306 A B x'' _46303 s)). Qed.
Lemma lem4012336 (a : Prop) : (term49 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4012337 {B : Type'} (_46303 : B) (t : B -> Prop) : (term338 B _46303 t) = (@IN B _46303 t).
Proof. exact (@lem4012336 (@IN B _46303 t)). Qed.
Lemma lem4012338 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4012339 {B : Type'} (_46303 : B) (t : B -> Prop) : (term339 B _46303 t) = (term75 B _46303 t).
Proof. exact (MK_COMB (@lem4012338) (@lem4012337 B _46303 t)). Qed.
Lemma lem4012340 {A B : Type'} (x'' : B -> A) (_46303 : B) (s : A -> Prop) : (term306 A B x'' _46303 s) = (term306 A B x'' _46303 s).
Proof. exact (eq_refl (term306 A B x'' _46303 s)). Qed.
Lemma lem4012341 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (_46303 : B) (s : A -> Prop) : (term373 A B t x'' _46303 s) = (term374 A B t x'' _46303 s).
Proof. exact (MK_COMB (@lem4012339 B _46303 t) (@lem4012340 A B x'' _46303 s)). Qed.
Lemma lem4012342 {A B : Type'} (t : B -> Prop) (x'' : B -> A) (_46303 : B) (s : A -> Prop) : (term370 A B x'' s _46303 t) = (term374 A B t x'' _46303 s).
Proof. exact (TRANS (@lem4012334 A B t x'' _46303 s) (@lem4012341 A B t x'' _46303 s)). Qed.
Lemma lem4012345 {A B : Type'} (_46303 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term374 A B t x'' _46303 s.
Proof. exact (EQ_MP (@lem4012342 A B t x'' _46303 s) (@lem4012331 A B _46303 t x'' s f h1)). Qed.
Lemma lem4012346 {A B : Type'} (_46303 : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term374 A B t x'' _46303 s.
Proof. exact (@lem4012345 A B _46303 t x'' s f h1). Qed.
Lemma lem4012347 {A B : Type'} (x : B) (t : B -> Prop) (x'' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x'' s f) : term374 A B t x'' x s.
Proof. exact (@lem4012346 A B x t x'' s f h1). Qed.
Lemma lem4012350 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term189 A B t x'' s f) (h2 : term208 A B t x f s) : term306 A B x'' x s.
Proof. exact (@lem4012347 A B x t x'' s f h1 (@lem4012302 A B t x f s h2)). Qed.
Lemma lem4012351 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term189 A B t x'' s f) (h2 : term208 A B t x f s) : term375 A B x'' x s.
Proof. exact (fun h0 : term376 A B x'' x s => @lem4012350 A B x'' t x f s h1 h2). Qed.
Lemma lem4012353 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4012354 {A B : Type'} (x'' : B -> A) (x : B) (s : A -> Prop) : (term375 A B x'' x s) = (term306 A B x'' x s).
Proof. exact (@lem4012353 (term306 A B x'' x s)). Qed.
Lemma lem4012355 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term189 A B t x'' s f) (h2 : term208 A B t x f s) : term306 A B x'' x s.
Proof. exact (EQ_MP (@lem4012354 A B x'' x s) (@lem4012351 A B x'' t x f s h1 h2)). Qed.
Lemma lem4012357 (a : Prop) (b : Prop) : (term377 a b) = (term378 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4012358 {A B : Type'} (x : B) (f : A -> B) (_46306 : A) (s : A -> Prop) : (term194 A B x f _46306 s) = (term193 A B x f _46306 s).
Proof. exact (@lem4012357 (x = (f _46306)) (@IN A _46306 s)). Qed.
Lemma lem4012360 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4012361 {A B : Type'} (x : B) (f : A -> B) (_46306 : A) (s : A -> Prop) : (term193 A B x f _46306 s) = (term379 A B x f _46306 s).
Proof. exact (@lem4012360 (term70 A B x f _46306 s)). Qed.
Lemma lem4012362 {A B : Type'} (x : B) (f : A -> B) (_46306 : A) (s : A -> Prop) : (term194 A B x f _46306 s) = (term379 A B x f _46306 s).
Proof. exact (TRANS (@lem4012358 A B x f _46306 s) (@lem4012361 A B x f _46306 s)). Qed.
Lemma lem4012364 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term189 A B t x'' s f) (h2 : term208 A B t x f s) : term380 A B f x'' x s.
Proof. exact (conj (@lem4012295 A B x'' t x f s h1 h2) (@lem4012355 A B x'' t x f s h1 h2)). Qed.
Lemma lem4012366 {A B : Type'} (_46306 : A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term208 A B t x f s) : term379 A B x f _46306 s.
Proof. exact (EQ_MP (@lem4012362 A B x f _46306 s) (@lem4011822 A B _46306 t x f s h1)). Qed.
Lemma lem4012367 {A B : Type'} (_46306 : A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term208 A B t x f s) : term379 A B x f _46306 s.
Proof. exact (@lem4012366 A B _46306 t x f s h1). Qed.
Lemma lem4012368 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term208 A B t x f s) : term381 A B f x'' x s.
Proof. exact (@lem4012367 A B (x'' x) t x f s h1). Qed.
Lemma lem4012371 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term189 A B t x'' s f) (h2 : term208 A B t x f s) : False.
Proof. exact (@lem4012368 A B x'' t x f s h2 (@lem4012364 A B x'' t x f s h1 h2)). Qed.
Lemma lem4012372 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term189 A B t x'' s f) (h2 : term208 A B t x f s) : term382.
Proof. exact (fun h0 : ~ False => @lem4012371 A B x'' t x f s h1 h2). Qed.
Lemma lem4012374 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4012375 : term382 = False.
Proof. exact (@lem4012374 False). Qed.
Lemma lem4012376 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term189 A B t x'' s f) (h2 : term208 A B t x f s) : False.
Proof. exact (EQ_MP (@lem4012375) (@lem4012372 A B x'' t x f s h1 h2)). Qed.
Lemma lem4012452 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term222 A B t x f x' s) : @IN A x' s.
Proof. exact (proj2 (@lem4011341 A B t x f x' s h1)). Qed.
Lemma lem4012453 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term222 A B t x f x' s) : term331 A x' s.
Proof. exact (fun h0 : term155 A x' s => @lem4012452 A B t x f x' s h1). Qed.
Lemma lem4012455 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4012456 {A : Type'} (x' : A) (s : A -> Prop) : (term331 A x' s) = (@IN A x' s).
Proof. exact (@lem4012455 (@IN A x' s)). Qed.
Lemma lem4012457 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term222 A B t x f x' s) : @IN A x' s.
Proof. exact (EQ_MP (@lem4012456 A x' s) (@lem4012453 A B t x f x' s h1)). Qed.
Lemma lem4012463 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4012464 {A B : Type'} (f : A -> B) (t : B -> Prop) (_46307 : A) (s : A -> Prop) : (term82 A B s f _46307 t) = (term383 A B f t _46307 s).
Proof. exact (@lem4012463 (term83 A B f _46307 t) (term155 A _46307 s)). Qed.
Lemma lem4012470 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4012471 {A B : Type'} (f : A -> B) (t : B -> Prop) (_46307 : A) (s : A -> Prop) : (term384 A B s f _46307 t) = (term385 A B f t _46307 s).
Proof. exact (MK_COMB (@lem4012470) (@lem4012464 A B f t _46307 s)). Qed.
Lemma lem4012477 {A B : Type'} (f : A -> B) (t : B -> Prop) (_46307 : A) (s : A -> Prop) : (term383 A B f t _46307 s) = (term383 A B f t _46307 s).
Proof. exact (eq_refl (term383 A B f t _46307 s)). Qed.
Lemma lem4012478 {A B : Type'} (f : A -> B) (t : B -> Prop) (_46307 : A) (s : A -> Prop) : ((term82 A B s f _46307 t) = (term383 A B f t _46307 s)) = ((term383 A B f t _46307 s) = (term383 A B f t _46307 s)).
Proof. exact (MK_COMB (@lem4012471 A B f t _46307 s) (@lem4012477 A B f t _46307 s)). Qed.
Lemma lem4012480 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4012481 (x : Prop) : (x = x) = True.
Proof. exact (@lem4012480 Prop x). Qed.
Lemma lem4012482 {A B : Type'} (f : A -> B) (t : B -> Prop) (_46307 : A) (s : A -> Prop) : ((term383 A B f t _46307 s) = (term383 A B f t _46307 s)) = True.
Proof. exact (@lem4012481 (term383 A B f t _46307 s)). Qed.
Lemma lem4012483 {A B : Type'} (f : A -> B) (t : B -> Prop) (_46307 : A) (s : A -> Prop) : ((term82 A B s f _46307 t) = (term383 A B f t _46307 s)) = True.
Proof. exact (TRANS (@lem4012478 A B f t _46307 s) (@lem4012482 A B f t _46307 s)). Qed.
Lemma lem4012484 {A B : Type'} (f : A -> B) (t : B -> Prop) (_46307 : A) (s : A -> Prop) : True = ((term82 A B s f _46307 t) = (term383 A B f t _46307 s)).
Proof. exact (SYM (@lem4012483 A B f t _46307 s)). Qed.
Lemma lem4012485 {A B : Type'} (f : A -> B) (t : B -> Prop) (_46307 : A) (s : A -> Prop) : (term82 A B s f _46307 t) = (term383 A B f t _46307 s).
Proof. exact (EQ_MP (@lem4012484 A B f t _46307 s) (@lem0)). Qed.
Lemma lem4012486 {A B : Type'} (_46307 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term383 A B f t _46307 s.
Proof. exact (EQ_MP (@lem4012485 A B f t _46307 s) (@lem4011954 A B _46307 s f t h1)). Qed.
Lemma lem4012488 (b : Prop) (a : Prop) : (a \/ b) = (term336 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4012489 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46307 : A) (t : B -> Prop) : (term383 A B f t _46307 s) = (term386 A B s f _46307 t).
Proof. exact (@lem4012488 (term155 A _46307 s) (term83 A B f _46307 t)). Qed.
Lemma lem4012491 (a : Prop) : (term49 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4012492 {A : Type'} (_46307 : A) (s : A -> Prop) : (term338 A _46307 s) = (@IN A _46307 s).
Proof. exact (@lem4012491 (@IN A _46307 s)). Qed.
Lemma lem4012493 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4012494 {A : Type'} (_46307 : A) (s : A -> Prop) : (term339 A _46307 s) = (term75 A _46307 s).
Proof. exact (MK_COMB (@lem4012493) (@lem4012492 A _46307 s)). Qed.
Lemma lem4012495 {A B : Type'} (f : A -> B) (_46307 : A) (t : B -> Prop) : (term83 A B f _46307 t) = (term83 A B f _46307 t).
Proof. exact (eq_refl (term83 A B f _46307 t)). Qed.
Lemma lem4012496 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46307 : A) (t : B -> Prop) : (term386 A B s f _46307 t) = (term78 A B s f _46307 t).
Proof. exact (MK_COMB (@lem4012494 A _46307 s) (@lem4012495 A B f _46307 t)). Qed.
Lemma lem4012497 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46307 : A) (t : B -> Prop) : (term383 A B f t _46307 s) = (term78 A B s f _46307 t).
Proof. exact (TRANS (@lem4012489 A B s f _46307 t) (@lem4012496 A B s f _46307 t)). Qed.
Lemma lem4012500 {A B : Type'} (_46307 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term78 A B s f _46307 t.
Proof. exact (EQ_MP (@lem4012497 A B s f _46307 t) (@lem4012486 A B _46307 s f t h1)). Qed.
Lemma lem4012501 {A B : Type'} (_46307 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term78 A B s f _46307 t.
Proof. exact (@lem4012500 A B _46307 s f t h1). Qed.
Lemma lem4012502 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term78 A B s f x' t.
Proof. exact (@lem4012501 A B x' s f t h1). Qed.
Lemma lem4012505 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term222 A B t x f x' s) : term83 A B f x' t.
Proof. exact (@lem4012502 A B x' s f t h1 (@lem4012457 A B t x f x' s h2)). Qed.
Lemma lem4012506 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term222 A B t x f x' s) : term387 A B f x' t.
Proof. exact (fun h0 : term327 A B f x' t => @lem4012505 A B t x f x' s h1 h2). Qed.
Lemma lem4012508 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4012509 {A B : Type'} (f : A -> B) (x' : A) (t : B -> Prop) : (term387 A B f x' t) = (term83 A B f x' t).
Proof. exact (@lem4012508 (term83 A B f x' t)). Qed.
Lemma lem4012510 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term222 A B t x f x' s) : term83 A B f x' t.
Proof. exact (EQ_MP (@lem4012509 A B f x' t) (@lem4012506 A B t x f x' s h1 h2)). Qed.
Lemma lem4012513 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4012515 {A B : Type'} (f : A -> B) (x' : A) (t : B -> Prop) : (term327 A B f x' t) = (term388 A B f x' t).
Proof. exact (@lem4012513 (term83 A B f x' t)). Qed.
Lemma lem4012518 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term222 A B t x f x' s) : term388 A B f x' t.
Proof. exact (EQ_MP (@lem4012515 A B f x' t) (@lem4011967 A B t x f x' s h1)). Qed.
Lemma lem4012521 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term222 A B t x f x' s) : False.
Proof. exact (@lem4012518 A B t x f x' s h2 (@lem4012510 A B t x f x' s h1 h2)). Qed.
Lemma lem4012522 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term222 A B t x f x' s) : term382.
Proof. exact (fun h0 : ~ False => @lem4012521 A B t x f x' s h1 h2). Qed.
Lemma lem4012524 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4012525 : term382 = False.
Proof. exact (@lem4012524 False). Qed.
Lemma lem4012527 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term222 A B t x f x' s) : False.
Proof. exact (EQ_MP (@lem4012525) (@lem4012522 A B t x f x' s h1 h2)). Qed.
Lemma lem4012528 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term189 A B t x'' s f) (h3 : term235 A B t x f x' s) : False.
Proof. exact (or_elim (@lem4011245 A B t x f x' s h3) (fun h0 : term208 A B t x f s => @lem4012376 A B x'' t x f s h2 h0) (fun h0 : term222 A B t x f x' s => @lem4012527 A B t x f x' s h1 h0)). Qed.
Lemma lem4012529 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term189 A B t x'' s f) (h3 : term235 A B t x f x' s) : (term189 A B t x'' s f) = False.
Proof. exact (prop_ext (fun h4 : term189 A B t x'' s f => @lem4012528 A B x'' t x f x' s h1 h2 h3) (fun h4 : False => @lem4011336 A B t x'' s f h2)). Qed.
Lemma lem4012530 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term189 A B t x'' s f) (h3 : term235 A B t x f x' s) : False.
Proof. exact (EQ_MP (@lem4012529 A B x'' t x f x' s h1 h2 h3) (@lem4011336 A B t x'' s f h2)). Qed.
Lemma lem4012531 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term189 A B t x'' s f) (h3 : term235 A B t x f x' s) : (term235 A B t x f x' s) = False.
Proof. exact (prop_ext (fun h4 : term235 A B t x f x' s => @lem4012530 A B x'' t x f x' s h1 h2 h3) (fun h4 : False => @lem4011245 A B t x f x' s h3)). Qed.
Lemma lem4012532 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term189 A B t x'' s f) (h3 : term235 A B t x f x' s) : False.
Proof. exact (EQ_MP (@lem4012531 A B x'' t x f x' s h1 h2 h3) (@lem4011245 A B t x f x' s h3)). Qed.
Lemma lem4012533 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : term235 A B t x f x' s) : False.
Proof. exact (ex_elim (@lem4010978 A B t s f h2) (fun x'' : B -> A => fun h0 : term191 A B t s f x'' => @lem4012532 A B x'' t x f x' s h1 h0 h3)). Qed.
Lemma lem4012534 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : term81 A B t x f s) : False.
Proof. exact (ex_elim (@lem4011159 A B t x f s h3) (fun x' : A => fun h0 : term237 A B t x f s x' => @lem4012533 A B t x f x' s h1 h2 h0)). Qed.
Lemma lem4012535 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : term81 A B t x f s) : (term81 A B t x f s) = False.
Proof. exact (prop_ext (fun h4 : term81 A B t x f s => @lem4012534 A B t x f s h1 h2 h3) (fun h4 : False => @lem4010497 A B t x f s h3)). Qed.
Lemma lem4012536 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : term81 A B t x f s) : False.
Proof. exact (EQ_MP (@lem4012535 A B t x f s h1 h2 h3) (@lem4010497 A B t x f s h3)). Qed.
Lemma lem4012537 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term30 A B s f t) (h2 : term29 A B t s f) : term80 A B t x f s.
Proof. exact (fun h0 : term81 A B t x f s => @lem4012536 A B t x f s h1 h2 h0). Qed.
Lemma lem4012538 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term30 A B s f t) (h2 : term29 A B t s f) : (@IN B x t) = (term22 A B x f s).
Proof. exact (EQ_MP (@lem4010496 A B t x f s) (@lem4012537 A B x t s f h1 h2)). Qed.
Lemma lem4012543 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term30 A B s f t) (h2 : term29 A B t s f) : term40 A B t f s.
Proof. exact (fun x : B => @lem4012538 A B x t s f h1 h2). Qed.
Lemma lem4012544 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term52 A B t f s.
Proof. exact (fun h0 : term29 A B t s f => @lem4012543 A B t s f h1 h0). Qed.
Lemma lem4012545 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term55 A B t f s.
Proof. exact (fun h0 : term30 A B s f t => @lem4012544 A B s f t h0). Qed.
Lemma lem4012546 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term57 A B t f s.
Proof. exact (fun h0 : @FINITE A s => @lem4012545 A B t f s). Qed.
Lemma lem4012551 {A B : Type'} (f : A -> B) (s : A -> Prop) : term61 A B f s.
Proof. exact (fun t : B -> Prop => @lem4012546 A B t f s). Qed.
Lemma lem4012556 {A B : Type'} (s : A -> Prop) : term65 A B s.
Proof. exact (fun f : A -> B => @lem4012551 A B f s). Qed.
Lemma lem4012561 {A B : Type'} : term69 A B.
Proof. exact (fun s : A -> Prop => @lem4012556 A B s). Qed.
Lemma lem4012562 {A B : Type'} : term68 A B.
Proof. exact (EQ_MP (@lem4010489 A B) (@lem4012561 A B)). Qed.
Lemma lem4012563 {A B : Type'} (s : A -> Prop) : term389 A B s.
Proof. exact (@lem4012562 A B s). Qed.
Lemma lem4012564 {A B : Type'} (s : A -> Prop) : (term389 A B s) = (term64 A B s).
Proof. exact (eq_refl (term389 A B s)). Qed.
Lemma lem4012565 {A B : Type'} (s : A -> Prop) : term64 A B s.
Proof. exact (EQ_MP (@lem4012564 A B s) (@lem4012563 A B s)). Qed.
Lemma lem4012566 {A B : Type'} (s : A -> Prop) (f : A -> B) : term390 A B s f.
Proof. exact (@lem4012565 A B s f). Qed.
Lemma lem4012567 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term390 A B s f) = (term60 A B f s).
Proof. exact (eq_refl (term390 A B s f)). Qed.
Lemma lem4012568 {A B : Type'} (f : A -> B) (s : A -> Prop) : term60 A B f s.
Proof. exact (EQ_MP (@lem4012567 A B f s) (@lem4012566 A B s f)). Qed.
Lemma lem4012569 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : term391 A B f s t.
Proof. exact (@lem4012568 A B f s t). Qed.
Lemma lem4012570 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term391 A B f s t) = (term44 A B t f s).
Proof. exact (eq_refl (term391 A B f s t)). Qed.
Lemma lem4012571 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term44 A B t f s.
Proof. exact (EQ_MP (@lem4012570 A B t f s) (@lem4012569 A B f s t)). Qed.
Lemma lem4012573 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term44 A B t f s.
Proof. exact (@lem4010242 A B t f s (@lem4012571 A B t f s)). Qed.
Lemma lem4012574 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term54 A B t f s.
Proof. exact (@lem4012573 A B t f s (@lem4010162 A s h1)). Qed.
Lemma lem4012575 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : @FINITE A s) : term51 A B t f s.
Proof. exact (@lem4012574 A B t f s h2 (@lem4010164 A B s f t h1)). Qed.
Lemma lem4012576 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) : term42 A B t f s.
Proof. exact (@lem4012575 A B f t s h1 h3 (@lem4010163 A B t s f h2)). Qed.
Lemma lem4012577 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) (h4 : term43 A B t f s) : False.
Proof. exact (@lem4012576 A B t f s h1 h2 h3 (@lem4010226 A B t f s h4)). Qed.
Lemma lem4012578 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) (h4 : term43 A B t f s) : (term43 A B t f s) = False.
Proof. exact (prop_ext (fun h5 : term43 A B t f s => @lem4012577 A B t f s h1 h2 h3 h4) (fun h5 : False => @lem4010226 A B t f s h4)). Qed.
Lemma lem4012579 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) (h4 : term43 A B t f s) : False.
Proof. exact (EQ_MP (@lem4012578 A B t f s h1 h2 h3 h4) (@lem4010226 A B t f s h4)). Qed.
Lemma lem4012580 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) : term42 A B t f s.
Proof. exact (fun h0 : term43 A B t f s => @lem4012579 A B t f s h1 h2 h3 h0). Qed.
Lemma lem4012581 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) : term40 A B t f s.
Proof. exact (EQ_MP (@lem4010225 A B t f s) (@lem4012580 A B t f s h1 h2 h3)). Qed.
Lemma lem4012582 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) : t = (@IMAGE A B f s).
Proof. exact (EQ_MP (@lem4010221 A B t f s) (@lem4012581 A B t f s h1 h2 h3)). Qed.
Lemma lem4012584 {A B : Type'} (f : A -> B) (s : A -> Prop) : term11 A B f s.
Proof. exact (EQ_MP (@lem4010133 A B f s) (@lem4010132 A B f s)). Qed.
Lemma lem4012585 {A B : Type'} (f : A -> B) (s : A -> Prop) : term11 A B f s.
Proof. exact (@lem4012584 A B f s). Qed.
Lemma lem4012587 (p : Prop) : p = (term41 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4012588 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term12 A B f s) = (term392 A B f s).
Proof. exact (@lem4012587 (term12 A B f s)). Qed.
Lemma lem4012589 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term392 A B f s) = (term12 A B f s).
Proof. exact (SYM (@lem4012588 A B f s)). Qed.
Lemma lem4012590 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term393 A B f s) : term393 A B f s.
Proof. exact (h1). Qed.
Lemma lem4012593 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term394 A B t f s) : term394 A B t f s.
Proof. exact (h1). Qed.
Lemma lem4012594 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term395 A B t f s.
Proof. exact (fun h0 : term394 A B t f s => @lem4012593 A B t f s h0). Qed.
Lemma lem4012595 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term395 A B t f s) : term395 A B t f s.
Proof. exact (h1). Qed.
Lemma lem4012596 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term394 A B t f s) : term394 A B t f s.
Proof. exact (h1). Qed.
Lemma lem4012597 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term394 A B t f s) (h2 : term395 A B t f s) : term394 A B t f s.
Proof. exact (@lem4012595 A B t f s h2 (@lem4012596 A B t f s h1)). Qed.
Lemma lem4012598 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term394 A B t f s) : term396 A B t f s.
Proof. exact (fun h0 : term395 A B t f s => @lem4012597 A B t f s h1 h0). Qed.
Lemma lem4012599 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term395 A B t f s) : term395 A B t f s.
Proof. exact (h1). Qed.
Lemma lem4012600 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term394 A B t f s) (h2 : term395 A B t f s) : term394 A B t f s.
Proof. exact (@lem4012598 A B t f s h1 (@lem4012599 A B t f s h2)). Qed.
Lemma lem4012601 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term395 A B t f s) : term395 A B t f s.
Proof. exact (fun h0 : term394 A B t f s => @lem4012600 A B t f s h0 h1). Qed.
Lemma lem4012602 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term397 A B t f s.
Proof. exact (fun h0 : term395 A B t f s => @lem4012601 A B t f s h0). Qed.
Lemma lem4012605 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term395 A B t f s.
Proof. exact (@lem4012602 A B t f s (@lem4012594 A B t f s)). Qed.
Lemma lem4012606 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term395 A B t f s.
Proof. exact (@lem4012605 A B t f s). Qed.
Lemma lem4012640 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4012641 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term392 A B f s) = (term398 A B f s).
Proof. exact (@lem4012640 (term393 A B f s)). Qed.
Lemma lem4012643 (t : Prop) : (term49 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4012644 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term398 A B f s) = (term12 A B f s).
Proof. exact (@lem4012643 (term12 A B f s)). Qed.
Lemma lem4012647 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term392 A B f s) = (term12 A B f s).
Proof. exact (TRANS (@lem4012641 A B f s) (@lem4012644 A B f s)). Qed.
Lemma lem4012662 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term50 A B t s f) = (term50 A B t s f).
Proof. exact (eq_refl (term50 A B t s f)). Qed.
Lemma lem4012663 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term399 A B t f s) = (term400 A B t f s).
Proof. exact (MK_COMB (@lem4012662 A B t s f) (@lem4012647 A B f s)). Qed.
Lemma lem4012666 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term53 A B s f t) = (term53 A B s f t).
Proof. exact (eq_refl (term53 A B s f t)). Qed.
Lemma lem4012667 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term401 A B t f s) = (term402 A B t f s).
Proof. exact (MK_COMB (@lem4012666 A B s f t) (@lem4012663 A B t f s)). Qed.
Lemma lem4012670 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (eq_refl (term56 A s)). Qed.
Lemma lem4012671 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term394 A B t f s) = (term403 A B t f s).
Proof. exact (MK_COMB (@lem4012670 A s) (@lem4012667 A B t f s)). Qed.
Lemma lem4012674 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term404 A B f s) = (term405 A B f s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4012671 A B t f s)). Qed.
Lemma lem4012675 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4012676 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term406 A B f s) = (term407 A B f s).
Proof. exact (MK_COMB (@lem4012675 B) (@lem4012674 A B f s)). Qed.
Lemma lem4012681 {A B : Type'} (s : A -> Prop) : (term408 A B s) = (term409 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem4012676 A B f s)). Qed.
Lemma lem4012682 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4012683 {A B : Type'} (s : A -> Prop) : (term410 A B s) = (term411 A B s).
Proof. exact (MK_COMB (@lem4012682 A B) (@lem4012681 A B s)). Qed.
Lemma lem4012688 {A B : Type'} : (term412 A B) = (term413 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4012683 A B s)). Qed.
Lemma lem4012689 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4012698 {A B : Type'} : (term414 A B) = (term415 A B).
Proof. exact (MK_COMB (@lem4012689 A) (@lem4012688 A B)). Qed.
Lemma lem4012699 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem4012712 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term416 A B s f x y) = (term416 A B s f x y).
Proof. exact (eq_refl (term416 A B s f x y)). Qed.
Lemma lem4012713 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term417 A B s f x) = (term417 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4012712 A B s f x y)). Qed.
Lemma lem4012714 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4012715 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term418 A B s f x) = (term418 A B s f x).
Proof. exact (MK_COMB (@lem4012714 A) (@lem4012713 A B s f x)). Qed.
Lemma lem4012716 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term419 A B s f) = (term419 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4012715 A B s f x)). Qed.
Lemma lem4012717 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4012718 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term420 A B s f) = (term420 A B s f).
Proof. exact (MK_COMB (@lem4012717 A) (@lem4012716 A B s f)). Qed.
Lemma lem4012719 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4012720 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term421 A B s f) = (term421 A B s f).
Proof. exact (MK_COMB (@lem4012719) (@lem4012718 A B s f)). Qed.
Lemma lem4012721 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term12 A B f s) = (term12 A B f s).
Proof. exact (MK_COMB (@lem4012720 A B s f) (@lem4012699 A s)). Qed.
Lemma lem4012726 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term72 A B s f x y) = (term72 A B s f x y).
Proof. exact (eq_refl (term72 A B s f x y)). Qed.
Lemma lem4012727 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term73 A B s f y) = (term73 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4012726 A B s f x y)). Qed.
Lemma lem4012728 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem4012729 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term74 A B s f y) = (term74 A B s f y).
Proof. exact (MK_COMB (@lem4012728 A) (@lem4012727 A B s f y)). Qed.
Lemma lem4012732 {B : Type'} (y : B) (t : B -> Prop) : (term75 B y t) = (term75 B y t).
Proof. exact (eq_refl (term75 B y t)). Qed.
Lemma lem4012733 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term76 A B t s f y) = (term76 A B t s f y).
Proof. exact (MK_COMB (@lem4012732 B y t) (@lem4012729 A B s f y)). Qed.
Lemma lem4012734 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term77 A B t s f) = (term77 A B t s f).
Proof. exact (fun_ext (fun y : B => @lem4012733 A B t s f y)). Qed.
Lemma lem4012735 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4012736 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term29 A B t s f) = (term29 A B t s f).
Proof. exact (MK_COMB (@lem4012735 B) (@lem4012734 A B t s f)). Qed.
Lemma lem4012737 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4012738 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term50 A B t s f) = (term50 A B t s f).
Proof. exact (MK_COMB (@lem4012737) (@lem4012736 A B t s f)). Qed.
Lemma lem4012739 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term400 A B t f s) = (term400 A B t f s).
Proof. exact (MK_COMB (@lem4012738 A B t s f) (@lem4012721 A B f s)). Qed.
Lemma lem4012744 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term78 A B s f x t) = (term78 A B s f x t).
Proof. exact (eq_refl (term78 A B s f x t)). Qed.
Lemma lem4012745 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term79 A B s f t) = (term79 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem4012744 A B s f x t)). Qed.
Lemma lem4012746 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4012747 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term30 A B s f t) = (term30 A B s f t).
Proof. exact (MK_COMB (@lem4012746 A) (@lem4012745 A B s f t)). Qed.
Lemma lem4012748 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4012749 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term53 A B s f t) = (term53 A B s f t).
Proof. exact (MK_COMB (@lem4012748) (@lem4012747 A B s f t)). Qed.
Lemma lem4012750 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term402 A B t f s) = (term402 A B t f s).
Proof. exact (MK_COMB (@lem4012749 A B s f t) (@lem4012739 A B t f s)). Qed.
Lemma lem4012753 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (eq_refl (term56 A s)). Qed.
Lemma lem4012754 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term403 A B t f s) = (term403 A B t f s).
Proof. exact (MK_COMB (@lem4012753 A s) (@lem4012750 A B t f s)). Qed.
Lemma lem4012755 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term405 A B f s) = (term405 A B f s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4012754 A B t f s)). Qed.
Lemma lem4012756 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4012757 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term407 A B f s) = (term407 A B f s).
Proof. exact (MK_COMB (@lem4012756 B) (@lem4012755 A B f s)). Qed.
Lemma lem4012758 {A B : Type'} (s : A -> Prop) : (term409 A B s) = (term409 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem4012757 A B f s)). Qed.
Lemma lem4012759 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4012760 {A B : Type'} (s : A -> Prop) : (term411 A B s) = (term411 A B s).
Proof. exact (MK_COMB (@lem4012759 A B) (@lem4012758 A B s)). Qed.
Lemma lem4012761 {A B : Type'} : (term413 A B) = (term413 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4012760 A B s)). Qed.
Lemma lem4012762 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4012763 {A B : Type'} : (term415 A B) = (term415 A B).
Proof. exact (MK_COMB (@lem4012762 A) (@lem4012761 A B)). Qed.
Lemma lem4012828 {A B : Type'} : (term414 A B) = (term415 A B).
Proof. exact (TRANS (@lem4012698 A B) (@lem4012763 A B)). Qed.
Lemma lem4012829 {A B : Type'} : (term415 A B) = (term414 A B).
Proof. exact (SYM (@lem4012828 A B)). Qed.
Lemma lem4012831 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term30 A B s f t.
Proof. exact (h1). Qed.
Lemma lem4012832 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term29 A B t s f) : term29 A B t s f.
Proof. exact (h1). Qed.
Lemma lem4012834 (p : Prop) : p = (term41 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4012835 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term12 A B f s) = (term392 A B f s).
Proof. exact (@lem4012834 (term12 A B f s)). Qed.
Lemma lem4012836 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term392 A B f s) = (term12 A B f s).
Proof. exact (SYM (@lem4012835 A B f s)). Qed.
Lemma lem4012837 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term393 A B f s) : term393 A B f s.
Proof. exact (h1). Qed.
Lemma lem4012843 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4012850 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term78 A B s f x t) = (term82 A B s f x t).
Proof. exact (@lem17265 (@IN A x s) (term83 A B f x t)). Qed.
Lemma lem4012851 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term79 A B s f t) = (term84 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem4012850 A B s f x t)). Qed.
Lemma lem4012852 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4012905 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term30 A B s f t) = (term85 A B s f t).
Proof. exact (MK_COMB (@lem4012852 A) (@lem4012851 A B s f t)). Qed.
Lemma lem4012906 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term85 A B s f t.
Proof. exact (EQ_MP (@lem4012905 A B s f t) (@lem4012831 A B s f t h1)). Qed.
Lemma lem4012916 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term86 A B s f x y) = (term87 A B s f x y).
Proof. exact (@lem17045 (@IN A x s) ((f x) = y)). Qed.
Lemma lem4012921 {A : Type'} (x' : A) (x : A) : (x' = x) = (x' = x).
Proof. exact (eq_refl (x' = x)). Qed.
Lemma lem4012922 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term88 A B s f y x) = (term72 A B s f x y).
Proof. exact (eq_refl (term88 A B s f y x)). Qed.
Lemma lem4012923 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) : (term88 A B s f y x') = (term72 A B s f x' y).
Proof. exact (eq_refl (term88 A B s f y x')). Qed.
Lemma lem4012924 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) : (term86 A B s f x' y) = (term87 A B s f x' y).
Proof. exact (@lem4012916 A B s f x' y). Qed.
Lemma lem4012925 {A : Type'} (P : A -> Prop) : (@ex1 A P) = (term89 A P).
Proof. exact (@lem18897 A P). Qed.
Lemma lem4012926 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term74 A B s f y) = (term90 A B s f y).
Proof. exact (@lem4012925 A (term73 A B s f y)). Qed.
Lemma lem4012927 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4012928 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) : (term91 A B s f y x') = (term86 A B s f x' y).
Proof. exact (MK_COMB (@lem4012927) (@lem4012923 A B s f x' y)). Qed.
Lemma lem4012929 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) : (term91 A B s f y x') = (term87 A B s f x' y).
Proof. exact (TRANS (@lem4012928 A B s f x' y) (@lem4012924 A B s f x' y)). Qed.
Lemma lem4012930 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4012931 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : B) : (term92 A B s f y x') = (term93 A B s f x' y).
Proof. exact (MK_COMB (@lem4012930) (@lem4012929 A B s f x' y)). Qed.
Lemma lem4012932 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term94 A B s f y x' x) = (term95 A B s f y x' x).
Proof. exact (MK_COMB (@lem4012931 A B s f x' y) (@lem4012921 A x' x)). Qed.
Lemma lem4012933 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4012934 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term91 A B s f y x) = (term86 A B s f x y).
Proof. exact (MK_COMB (@lem4012933) (@lem4012922 A B s f x y)). Qed.
Lemma lem4012935 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term91 A B s f y x) = (term87 A B s f x y).
Proof. exact (TRANS (@lem4012934 A B s f x y) (@lem4012916 A B s f x y)). Qed.
Lemma lem4012936 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4012937 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term92 A B s f y x) = (term93 A B s f x y).
Proof. exact (MK_COMB (@lem4012936) (@lem4012935 A B s f x y)). Qed.
Lemma lem4012938 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term96 A B s f y x' x) = (term97 A B s f y x' x).
Proof. exact (MK_COMB (@lem4012937 A B s f x y) (@lem4012932 A B s f y x' x)). Qed.
Lemma lem4012939 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term98 A B s f y x) = (term99 A B s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4012938 A B s f y x' x)). Qed.
Lemma lem4012940 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4012941 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term100 A B s f y x) = (term101 A B s f y x).
Proof. exact (MK_COMB (@lem4012940 A) (@lem4012939 A B s f y x)). Qed.
Lemma lem4012942 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term102 A B s f y) = (term103 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4012941 A B s f y x)). Qed.
Lemma lem4012943 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4012944 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term104 A B s f y) = (term105 A B s f y).
Proof. exact (MK_COMB (@lem4012943 A) (@lem4012942 A B s f y)). Qed.
Lemma lem4012945 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term88 A B s f y x) = (term72 A B s f x y).
Proof. exact (eq_refl (term88 A B s f y x)). Qed.
Lemma lem4012946 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term106 A B s f y) = (term73 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4012945 A B s f x y)). Qed.
Lemma lem4012947 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4012948 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term107 A B s f y) = (term108 A B s f y).
Proof. exact (MK_COMB (@lem4012947 A) (@lem4012946 A B s f y)). Qed.
Lemma lem4012949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4012950 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term109 A B s f y) = (term110 A B s f y).
Proof. exact (MK_COMB (@lem4012949) (@lem4012948 A B s f y)). Qed.
Lemma lem4012951 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term90 A B s f y) = (term111 A B s f y).
Proof. exact (MK_COMB (@lem4012950 A B s f y) (@lem4012944 A B s f y)). Qed.
Lemma lem4012952 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term74 A B s f y) = (term111 A B s f y).
Proof. exact (TRANS (@lem4012926 A B s f y) (@lem4012951 A B s f y)). Qed.
Lemma lem4012954 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4012955 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term113 A B t s f y) = (term114 A B t s f y).
Proof. exact (MK_COMB (@lem4012954 B y t) (@lem4012952 A B s f y)). Qed.
Lemma lem4012956 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term76 A B t s f y) = (term113 A B t s f y).
Proof. exact (@lem17265 (@IN B y t) (term74 A B s f y)). Qed.
Lemma lem4012957 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term76 A B t s f y) = (term114 A B t s f y).
Proof. exact (TRANS (@lem4012956 A B t s f y) (@lem4012955 A B t s f y)). Qed.
Lemma lem4012958 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term77 A B t s f) = (term115 A B t s f).
Proof. exact (fun_ext (fun y : B => @lem4012957 A B t s f y)). Qed.
Lemma lem4012959 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4012960 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term29 A B t s f) = (term116 A B t s f).
Proof. exact (MK_COMB (@lem4012959 B) (@lem4012958 A B t s f)). Qed.
Lemma lem4013062 {A : Type'} (P : Prop) (Q : A -> Prop) : (term117 A P Q) = (term118 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem4013063 {A : Type'} (P : Prop) (Q : A -> Prop) : (term117 A P Q) = (term118 A P Q).
Proof. exact (@lem4013062 A P Q). Qed.
Lemma lem4013064 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term119 A B s f y x) = (term120 A B s f y x).
Proof. exact (@lem4013063 A (term87 A B s f x y) (term121 A B s f y x)). Qed.
Lemma lem4013065 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term122 A B s f y x x') = (term95 A B s f y x' x).
Proof. exact (eq_refl (term122 A B s f y x x')). Qed.
Lemma lem4013066 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term93 A B s f x y) = (term93 A B s f x y).
Proof. exact (eq_refl (term93 A B s f x y)). Qed.
Lemma lem4013067 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term123 A B s f y x x') = (term97 A B s f y x' x).
Proof. exact (MK_COMB (@lem4013066 A B s f x y) (@lem4013065 A B s f y x' x)). Qed.
Lemma lem4013068 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term124 A B s f y x) = (term99 A B s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4013067 A B s f y x' x)). Qed.
Lemma lem4013069 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013070 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term119 A B s f y x) = (term101 A B s f y x).
Proof. exact (MK_COMB (@lem4013069 A) (@lem4013068 A B s f y x)). Qed.
Lemma lem4013071 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4013072 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term125 A B s f y x) = (term126 A B s f y x).
Proof. exact (MK_COMB (@lem4013071) (@lem4013070 A B s f y x)). Qed.
Lemma lem4013073 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term122 A B s f y x x') = (term95 A B s f y x' x).
Proof. exact (eq_refl (term122 A B s f y x x')). Qed.
Lemma lem4013074 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term127 A B s f y x) = (term121 A B s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4013073 A B s f y x' x)). Qed.
Lemma lem4013075 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013076 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term128 A B s f y x) = (term129 A B s f y x).
Proof. exact (MK_COMB (@lem4013075 A) (@lem4013074 A B s f y x)). Qed.
Lemma lem4013077 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term93 A B s f x y) = (term93 A B s f x y).
Proof. exact (eq_refl (term93 A B s f x y)). Qed.
Lemma lem4013078 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term120 A B s f y x) = (term130 A B s f y x).
Proof. exact (MK_COMB (@lem4013077 A B s f x y) (@lem4013076 A B s f y x)). Qed.
Lemma lem4013079 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : ((term119 A B s f y x) = (term120 A B s f y x)) = ((term101 A B s f y x) = (term130 A B s f y x)).
Proof. exact (MK_COMB (@lem4013072 A B s f y x) (@lem4013078 A B s f y x)). Qed.
Lemma lem4013080 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term101 A B s f y x) = (term130 A B s f y x).
Proof. exact (EQ_MP (@lem4013079 A B s f y x) (@lem4013064 A B s f y x)). Qed.
Lemma lem4013129 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term103 A B s f y) = (term131 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4013080 A B s f y x)). Qed.
Lemma lem4013130 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013131 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term105 A B s f y) = (term132 A B s f y).
Proof. exact (MK_COMB (@lem4013130 A) (@lem4013129 A B s f y)). Qed.
Lemma lem4013180 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term110 A B s f y) = (term110 A B s f y).
Proof. exact (eq_refl (term110 A B s f y)). Qed.
Lemma lem4013181 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term111 A B s f y) = (term133 A B s f y).
Proof. exact (MK_COMB (@lem4013180 A B s f y) (@lem4013131 A B s f y)). Qed.
Lemma lem4013182 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4013183 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term114 A B t s f y) = (term134 A B t s f y).
Proof. exact (MK_COMB (@lem4013182 B y t) (@lem4013181 A B s f y)). Qed.
Lemma lem4013184 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term115 A B t s f) = (term135 A B t s f).
Proof. exact (fun_ext (fun y : B => @lem4013183 A B t s f y)). Qed.
Lemma lem4013185 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4013186 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term116 A B t s f) = (term136 A B t s f).
Proof. exact (MK_COMB (@lem4013185 B) (@lem4013184 A B t s f)). Qed.
Lemma lem4013236 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4013237 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (@lem4013236 A P Q). Qed.
Lemma lem4013238 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term139 A B s f y) = (term140 A B s f y).
Proof. exact (@lem4013237 A (term73 A B s f y) (term132 A B s f y)). Qed.
Lemma lem4013239 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term88 A B s f y x) = (term72 A B s f x y).
Proof. exact (eq_refl (term88 A B s f y x)). Qed.
Lemma lem4013240 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term106 A B s f y) = (term73 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4013239 A B s f x y)). Qed.
Lemma lem4013241 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4013242 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term107 A B s f y) = (term108 A B s f y).
Proof. exact (MK_COMB (@lem4013241 A) (@lem4013240 A B s f y)). Qed.
Lemma lem4013243 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4013244 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term109 A B s f y) = (term110 A B s f y).
Proof. exact (MK_COMB (@lem4013243) (@lem4013242 A B s f y)). Qed.
Lemma lem4013245 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term132 A B s f y) = (term132 A B s f y).
Proof. exact (eq_refl (term132 A B s f y)). Qed.
Lemma lem4013246 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term139 A B s f y) = (term133 A B s f y).
Proof. exact (MK_COMB (@lem4013244 A B s f y) (@lem4013245 A B s f y)). Qed.
Lemma lem4013247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4013248 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term141 A B s f y) = (term142 A B s f y).
Proof. exact (MK_COMB (@lem4013247) (@lem4013246 A B s f y)). Qed.
Lemma lem4013249 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term88 A B s f y x) = (term72 A B s f x y).
Proof. exact (eq_refl (term88 A B s f y x)). Qed.
Lemma lem4013250 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4013251 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term143 A B s f y x) = (term144 A B s f x y).
Proof. exact (MK_COMB (@lem4013250) (@lem4013249 A B s f x y)). Qed.
Lemma lem4013252 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term132 A B s f y) = (term132 A B s f y).
Proof. exact (eq_refl (term132 A B s f y)). Qed.
Lemma lem4013253 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (y : B) : (term145 A B x s f y) = (term146 A B x s f y).
Proof. exact (MK_COMB (@lem4013251 A B s f x y) (@lem4013252 A B s f y)). Qed.
Lemma lem4013254 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term147 A B s f y) = (term148 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4013253 A B x s f y)). Qed.
Lemma lem4013255 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4013256 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term140 A B s f y) = (term149 A B s f y).
Proof. exact (MK_COMB (@lem4013255 A) (@lem4013254 A B s f y)). Qed.
Lemma lem4013257 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : ((term139 A B s f y) = (term140 A B s f y)) = ((term133 A B s f y) = (term149 A B s f y)).
Proof. exact (MK_COMB (@lem4013248 A B s f y) (@lem4013256 A B s f y)). Qed.
Lemma lem4013258 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term133 A B s f y) = (term149 A B s f y).
Proof. exact (EQ_MP (@lem4013257 A B s f y) (@lem4013238 A B s f y)). Qed.
Lemma lem4013259 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4013260 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term134 A B t s f y) = (term150 A B t s f y).
Proof. exact (MK_COMB (@lem4013259 B y t) (@lem4013258 A B s f y)). Qed.
Lemma lem4013262 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4013263 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (@lem4013262 A P Q). Qed.
Lemma lem4013264 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term153 A B t s f y) = (term154 A B t s f y).
Proof. exact (@lem4013263 A (term155 B y t) (term148 A B s f y)). Qed.
Lemma lem4013265 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (y : B) : (term156 A B s f y x) = (term146 A B x s f y).
Proof. exact (eq_refl (term156 A B s f y x)). Qed.
Lemma lem4013266 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term157 A B s f y) = (term148 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4013265 A B x s f y)). Qed.
Lemma lem4013267 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4013268 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term158 A B s f y) = (term149 A B s f y).
Proof. exact (MK_COMB (@lem4013267 A) (@lem4013266 A B s f y)). Qed.
Lemma lem4013269 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4013270 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term153 A B t s f y) = (term150 A B t s f y).
Proof. exact (MK_COMB (@lem4013269 B y t) (@lem4013268 A B s f y)). Qed.
Lemma lem4013271 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4013272 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term159 A B t s f y) = (term160 A B t s f y).
Proof. exact (MK_COMB (@lem4013271) (@lem4013270 A B t s f y)). Qed.
Lemma lem4013273 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (y : B) : (term156 A B s f y x) = (term146 A B x s f y).
Proof. exact (eq_refl (term156 A B s f y x)). Qed.
Lemma lem4013274 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4013275 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) (y : B) : (term161 A B t s f y x) = (term162 A B t x s f y).
Proof. exact (MK_COMB (@lem4013274 B y t) (@lem4013273 A B x s f y)). Qed.
Lemma lem4013276 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term163 A B t s f y) = (term164 A B t s f y).
Proof. exact (fun_ext (fun x : A => @lem4013275 A B t x s f y)). Qed.
Lemma lem4013277 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4013278 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term154 A B t s f y) = (term165 A B t s f y).
Proof. exact (MK_COMB (@lem4013277 A) (@lem4013276 A B t s f y)). Qed.
Lemma lem4013279 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : ((term153 A B t s f y) = (term154 A B t s f y)) = ((term150 A B t s f y) = (term165 A B t s f y)).
Proof. exact (MK_COMB (@lem4013272 A B t s f y) (@lem4013278 A B t s f y)). Qed.
Lemma lem4013280 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term150 A B t s f y) = (term165 A B t s f y).
Proof. exact (EQ_MP (@lem4013279 A B t s f y) (@lem4013264 A B t s f y)). Qed.
Lemma lem4013281 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term134 A B t s f y) = (term165 A B t s f y).
Proof. exact (TRANS (@lem4013260 A B t s f y) (@lem4013280 A B t s f y)). Qed.
Lemma lem4013282 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term135 A B t s f) = (term166 A B t s f).
Proof. exact (fun_ext (fun y : B => @lem4013281 A B t s f y)). Qed.
Lemma lem4013283 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4013284 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term136 A B t s f) = (term167 A B t s f).
Proof. exact (MK_COMB (@lem4013283 B) (@lem4013282 A B t s f)). Qed.
Lemma lem4013286 {A B : Type'} (P : type1413 A B) : (term168 A B P) = (term169 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4013287 {A B : Type'} (P : type1470 A B) : (term170 A B P) = (term171 A B P).
Proof. exact (@lem4013286 B A P). Qed.
Lemma lem4013288 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term172 A B t s f) = (term173 A B t s f).
Proof. exact (@lem4013287 A B (term174 A B t s f)). Qed.
Lemma lem4013289 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term175 A B t s f y) = (term164 A B t s f y).
Proof. exact (eq_refl (term175 A B t s f y)). Qed.
Lemma lem4013290 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4013291 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term176 A B t s f y x) = (term177 A B t s f y x).
Proof. exact (MK_COMB (@lem4013289 A B t s f y) (@lem4013290 A x)). Qed.
Lemma lem4013292 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) (y : B) : (term177 A B t s f y x) = (term162 A B t x s f y).
Proof. exact (eq_refl (term177 A B t s f y x)). Qed.
Lemma lem4013293 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) (y : B) : (term176 A B t s f y x) = (term162 A B t x s f y).
Proof. exact (TRANS (@lem4013291 A B t s f y x) (@lem4013292 A B t x s f y)). Qed.
Lemma lem4013294 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term178 A B t s f y) = (term164 A B t s f y).
Proof. exact (fun_ext (fun x : A => @lem4013293 A B t x s f y)). Qed.
Lemma lem4013295 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4013296 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term179 A B t s f y) = (term165 A B t s f y).
Proof. exact (MK_COMB (@lem4013295 A) (@lem4013294 A B t s f y)). Qed.
Lemma lem4013297 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term180 A B t s f) = (term166 A B t s f).
Proof. exact (fun_ext (fun y : B => @lem4013296 A B t s f y)). Qed.
Lemma lem4013298 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4013299 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term172 A B t s f) = (term167 A B t s f).
Proof. exact (MK_COMB (@lem4013298 B) (@lem4013297 A B t s f)). Qed.
Lemma lem4013300 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4013301 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term181 A B t s f) = (term182 A B t s f).
Proof. exact (MK_COMB (@lem4013300) (@lem4013299 A B t s f)). Qed.
Lemma lem4013302 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term175 A B t s f y) = (term164 A B t s f y).
Proof. exact (eq_refl (term175 A B t s f y)). Qed.
Lemma lem4013303 {A B : Type'} (x : B -> A) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem4013304 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B -> A) (y : B) : (term183 A B t s f x y) = (term184 A B t s f x y).
Proof. exact (MK_COMB (@lem4013302 A B t s f y) (@lem4013303 A B x y)). Qed.
Lemma lem4013305 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term184 A B t s f x y) = (term185 A B t x s f y).
Proof. exact (eq_refl (term184 A B t s f x y)). Qed.
Lemma lem4013306 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term183 A B t s f x y) = (term185 A B t x s f y).
Proof. exact (TRANS (@lem4013304 A B t s f x y) (@lem4013305 A B t x s f y)). Qed.
Lemma lem4013307 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) : (term186 A B t s f x) = (term187 A B t x s f).
Proof. exact (fun_ext (fun y : B => @lem4013306 A B t x s f y)). Qed.
Lemma lem4013308 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4013309 {A B : Type'} (t : B -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) : (term188 A B t s f x) = (term189 A B t x s f).
Proof. exact (MK_COMB (@lem4013308 B) (@lem4013307 A B t x s f)). Qed.
Lemma lem4013310 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term190 A B t s f) = (term191 A B t s f).
Proof. exact (fun_ext (fun x : B -> A => @lem4013309 A B t x s f)). Qed.
Lemma lem4013311 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem4013312 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term173 A B t s f) = (term192 A B t s f).
Proof. exact (MK_COMB (@lem4013311 A B) (@lem4013310 A B t s f)). Qed.
Lemma lem4013313 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : ((term172 A B t s f) = (term173 A B t s f)) = ((term167 A B t s f) = (term192 A B t s f)).
Proof. exact (MK_COMB (@lem4013301 A B t s f) (@lem4013312 A B t s f)). Qed.
Lemma lem4013314 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term167 A B t s f) = (term192 A B t s f).
Proof. exact (EQ_MP (@lem4013313 A B t s f) (@lem4013288 A B t s f)). Qed.
Lemma lem4013315 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term136 A B t s f) = (term192 A B t s f).
Proof. exact (TRANS (@lem4013284 A B t s f) (@lem4013314 A B t s f)). Qed.
Lemma lem4013316 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term116 A B t s f) = (term192 A B t s f).
Proof. exact (TRANS (@lem4013186 A B t s f) (@lem4013315 A B t s f)). Qed.
Lemma lem4013317 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term29 A B t s f) = (term192 A B t s f).
Proof. exact (TRANS (@lem4012960 A B t s f) (@lem4013316 A B t s f)). Qed.
Lemma lem4013318 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term29 A B t s f) : term192 A B t s f.
Proof. exact (EQ_MP (@lem4013317 A B t s f) (@lem4012832 A B t s f h1)). Qed.
Lemma lem4013333 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term422 A B s f x y) = (term423 A B s f x y).
Proof. exact (@lem17362 (term424 A B s x f y) (x = y)). Qed.
Lemma lem4013334 {A : Type'} (P : A -> Prop) : (term425 A P) = (term426 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4013335 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term427 A B s f x) = (term428 A B s f x).
Proof. exact (@lem4013334 A (term417 A B s f x)). Qed.
Lemma lem4013336 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term429 A B s f x y) = (term416 A B s f x y).
Proof. exact (eq_refl (term429 A B s f x y)). Qed.
Lemma lem4013337 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4013338 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term430 A B s f x y) = (term422 A B s f x y).
Proof. exact (MK_COMB (@lem4013337) (@lem4013336 A B s f x y)). Qed.
Lemma lem4013339 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term430 A B s f x y) = (term423 A B s f x y).
Proof. exact (TRANS (@lem4013338 A B s f x y) (@lem4013333 A B s f x y)). Qed.
Lemma lem4013340 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term431 A B s f x) = (term432 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4013339 A B s f x y)). Qed.
Lemma lem4013341 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4013342 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term428 A B s f x) = (term433 A B s f x).
Proof. exact (MK_COMB (@lem4013341 A) (@lem4013340 A B s f x)). Qed.
Lemma lem4013343 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term427 A B s f x) = (term433 A B s f x).
Proof. exact (TRANS (@lem4013335 A B s f x) (@lem4013342 A B s f x)). Qed.
Lemma lem4013344 {A : Type'} (P : A -> Prop) : (term425 A P) = (term426 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4013345 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term434 A B s f) = (term435 A B s f).
Proof. exact (@lem4013344 A (term419 A B s f)). Qed.
Lemma lem4013346 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term436 A B s f x) = (term418 A B s f x).
Proof. exact (eq_refl (term436 A B s f x)). Qed.
Lemma lem4013347 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4013348 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term437 A B s f x) = (term427 A B s f x).
Proof. exact (MK_COMB (@lem4013347) (@lem4013346 A B s f x)). Qed.
Lemma lem4013349 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term437 A B s f x) = (term433 A B s f x).
Proof. exact (TRANS (@lem4013348 A B s f x) (@lem4013343 A B s f x)). Qed.
Lemma lem4013350 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term438 A B s f) = (term439 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4013349 A B s f x)). Qed.
Lemma lem4013351 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4013352 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term435 A B s f) = (term440 A B s f).
Proof. exact (MK_COMB (@lem4013351 A) (@lem4013350 A B s f)). Qed.
Lemma lem4013353 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term434 A B s f) = (term440 A B s f).
Proof. exact (TRANS (@lem4013345 A B s f) (@lem4013352 A B s f)). Qed.
Lemma lem4013354 {A : Type'} (s : A -> Prop) : (term441 A s) = (term441 A s).
Proof. exact (eq_refl (term441 A s)). Qed.
Lemma lem4013355 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4013356 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term442 A B s f) = (term443 A B s f).
Proof. exact (MK_COMB (@lem4013355) (@lem4013353 A B s f)). Qed.
Lemma lem4013357 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term444 A B f s) = (term445 A B f s).
Proof. exact (MK_COMB (@lem4013356 A B s f) (@lem4013354 A s)). Qed.
Lemma lem4013358 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term393 A B f s) = (term444 A B f s).
Proof. exact (@lem17045 (term420 A B s f) (@FINITE A s)). Qed.
Lemma lem4013359 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term393 A B f s) = (term445 A B f s).
Proof. exact (TRANS (@lem4013358 A B f s) (@lem4013357 A B f s)). Qed.
Lemma lem4013414 {A : Type'} (P : A -> Prop) (Q : Prop) : (term446 A P Q) = (term447 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4013415 {A : Type'} (P : A -> Prop) (Q : Prop) : (term446 A P Q) = (term447 A P Q).
Proof. exact (@lem4013414 A P Q). Qed.
Lemma lem4013416 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term448 A B f s) = (term449 A B f s).
Proof. exact (@lem4013415 A (term439 A B s f) (term441 A s)). Qed.
Lemma lem4013417 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term450 A B s f x) = (term433 A B s f x).
Proof. exact (eq_refl (term450 A B s f x)). Qed.
Lemma lem4013418 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term451 A B s f) = (term439 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4013417 A B s f x)). Qed.
Lemma lem4013419 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4013420 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term452 A B s f) = (term440 A B s f).
Proof. exact (MK_COMB (@lem4013419 A) (@lem4013418 A B s f)). Qed.
Lemma lem4013421 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4013422 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term453 A B s f) = (term443 A B s f).
Proof. exact (MK_COMB (@lem4013421) (@lem4013420 A B s f)). Qed.
Lemma lem4013423 {A : Type'} (s : A -> Prop) : (term441 A s) = (term441 A s).
Proof. exact (eq_refl (term441 A s)). Qed.
Lemma lem4013424 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term448 A B f s) = (term445 A B f s).
Proof. exact (MK_COMB (@lem4013422 A B s f) (@lem4013423 A s)). Qed.
Lemma lem4013425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4013426 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term454 A B f s) = (term455 A B f s).
Proof. exact (MK_COMB (@lem4013425) (@lem4013424 A B f s)). Qed.
Lemma lem4013427 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term450 A B s f x) = (term433 A B s f x).
Proof. exact (eq_refl (term450 A B s f x)). Qed.
Lemma lem4013428 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4013429 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term456 A B s f x) = (term457 A B s f x).
Proof. exact (MK_COMB (@lem4013428) (@lem4013427 A B s f x)). Qed.
Lemma lem4013430 {A : Type'} (s : A -> Prop) : (term441 A s) = (term441 A s).
Proof. exact (eq_refl (term441 A s)). Qed.
Lemma lem4013431 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term458 A B f x s) = (term459 A B f x s).
Proof. exact (MK_COMB (@lem4013429 A B s f x) (@lem4013430 A s)). Qed.
Lemma lem4013432 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term460 A B f s) = (term461 A B f s).
Proof. exact (fun_ext (fun x : A => @lem4013431 A B f x s)). Qed.
Lemma lem4013433 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4013434 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term449 A B f s) = (term462 A B f s).
Proof. exact (MK_COMB (@lem4013433 A) (@lem4013432 A B f s)). Qed.
Lemma lem4013435 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term448 A B f s) = (term449 A B f s)) = ((term445 A B f s) = (term462 A B f s)).
Proof. exact (MK_COMB (@lem4013426 A B f s) (@lem4013434 A B f s)). Qed.
Lemma lem4013436 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term445 A B f s) = (term462 A B f s).
Proof. exact (EQ_MP (@lem4013435 A B f s) (@lem4013416 A B f s)). Qed.
Lemma lem4013438 {A : Type'} (P : A -> Prop) (Q : Prop) : (term446 A P Q) = (term447 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4013439 {A : Type'} (P : A -> Prop) (Q : Prop) : (term446 A P Q) = (term447 A P Q).
Proof. exact (@lem4013438 A P Q). Qed.
Lemma lem4013440 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term463 A B f x s) = (term464 A B f x s).
Proof. exact (@lem4013439 A (term432 A B s f x) (term441 A s)). Qed.
Lemma lem4013441 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term465 A B s f x y) = (term423 A B s f x y).
Proof. exact (eq_refl (term465 A B s f x y)). Qed.
Lemma lem4013442 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term466 A B s f x) = (term432 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4013441 A B s f x y)). Qed.
Lemma lem4013443 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4013444 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term467 A B s f x) = (term433 A B s f x).
Proof. exact (MK_COMB (@lem4013443 A) (@lem4013442 A B s f x)). Qed.
Lemma lem4013445 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4013446 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term468 A B s f x) = (term457 A B s f x).
Proof. exact (MK_COMB (@lem4013445) (@lem4013444 A B s f x)). Qed.
Lemma lem4013447 {A : Type'} (s : A -> Prop) : (term441 A s) = (term441 A s).
Proof. exact (eq_refl (term441 A s)). Qed.
Lemma lem4013448 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term463 A B f x s) = (term459 A B f x s).
Proof. exact (MK_COMB (@lem4013446 A B s f x) (@lem4013447 A s)). Qed.
Lemma lem4013449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4013450 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term469 A B f x s) = (term470 A B f x s).
Proof. exact (MK_COMB (@lem4013449) (@lem4013448 A B f x s)). Qed.
Lemma lem4013451 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term465 A B s f x y) = (term423 A B s f x y).
Proof. exact (eq_refl (term465 A B s f x y)). Qed.
Lemma lem4013452 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4013453 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term471 A B s f x y) = (term472 A B s f x y).
Proof. exact (MK_COMB (@lem4013452) (@lem4013451 A B s f x y)). Qed.
Lemma lem4013454 {A : Type'} (s : A -> Prop) : (term441 A s) = (term441 A s).
Proof. exact (eq_refl (term441 A s)). Qed.
Lemma lem4013455 {A B : Type'} (f : A -> B) (x : A) (y : A) (s : A -> Prop) : (term473 A B f x y s) = (term474 A B f x y s).
Proof. exact (MK_COMB (@lem4013453 A B s f x y) (@lem4013454 A s)). Qed.
Lemma lem4013456 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term475 A B f x s) = (term476 A B f x s).
Proof. exact (fun_ext (fun y : A => @lem4013455 A B f x y s)). Qed.
Lemma lem4013457 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4013458 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term464 A B f x s) = (term477 A B f x s).
Proof. exact (MK_COMB (@lem4013457 A) (@lem4013456 A B f x s)). Qed.
Lemma lem4013459 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : ((term463 A B f x s) = (term464 A B f x s)) = ((term459 A B f x s) = (term477 A B f x s)).
Proof. exact (MK_COMB (@lem4013450 A B f x s) (@lem4013458 A B f x s)). Qed.
Lemma lem4013460 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term459 A B f x s) = (term477 A B f x s).
Proof. exact (EQ_MP (@lem4013459 A B f x s) (@lem4013440 A B f x s)). Qed.
Lemma lem4013461 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term461 A B f s) = (term478 A B f s).
Proof. exact (fun_ext (fun x : A => @lem4013460 A B f x s)). Qed.
Lemma lem4013462 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4013463 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term462 A B f s) = (term479 A B f s).
Proof. exact (MK_COMB (@lem4013462 A) (@lem4013461 A B f s)). Qed.
Lemma lem4013465 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term445 A B f s) = (term479 A B f s).
Proof. exact (TRANS (@lem4013436 A B f s) (@lem4013463 A B f s)). Qed.
Lemma lem4013466 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term393 A B f s) = (term479 A B f s).
Proof. exact (TRANS (@lem4013359 A B f s) (@lem4013465 A B f s)). Qed.
Lemma lem4013467 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term393 A B f s) : term479 A B f s.
Proof. exact (EQ_MP (@lem4013466 A B f s) (@lem4012837 A B f s h1)). Qed.
Lemma lem4013468 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term477 A B f x s) : term477 A B f x s.
Proof. exact (h1). Qed.
Lemma lem4013470 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x' s f) : term189 A B t x' s f.
Proof. exact (h1). Qed.
Lemma lem4013474 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4013491 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term82 A B s f x t) = (term82 A B s f x t).
Proof. exact (eq_refl (term82 A B s f x t)). Qed.
Lemma lem4013492 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term84 A B s f t) = (term84 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem4013491 A B s f x t)). Qed.
Lemma lem4013493 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013494 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term85 A B s f t) = (term85 A B s f t).
Proof. exact (MK_COMB (@lem4013493 A) (@lem4013492 A B s f t)). Qed.
Lemma lem4013495 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term85 A B s f t.
Proof. exact (EQ_MP (@lem4013494 A B s f t) (@lem4012906 A B s f t h1)). Qed.
Lemma lem4013539 {A B : Type'} (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : term474 A B f x y s) : term474 A B f x y s.
Proof. exact (h1). Qed.
Lemma lem4013566 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term95 A B s f y x' x) = (term95 A B s f y x' x).
Proof. exact (eq_refl (term95 A B s f y x' x)). Qed.
Lemma lem4013567 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term121 A B s f y x) = (term121 A B s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4013566 A B s f y x' x)). Qed.
Lemma lem4013568 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013569 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term129 A B s f y x) = (term129 A B s f y x).
Proof. exact (MK_COMB (@lem4013568 A) (@lem4013567 A B s f y x)). Qed.
Lemma lem4013590 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term93 A B s f x y) = (term93 A B s f x y).
Proof. exact (eq_refl (term93 A B s f x y)). Qed.
Lemma lem4013591 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term130 A B s f y x) = (term130 A B s f y x).
Proof. exact (MK_COMB (@lem4013590 A B s f x y) (@lem4013569 A B s f y x)). Qed.
Lemma lem4013592 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term131 A B s f y) = (term131 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4013591 A B s f y x)). Qed.
Lemma lem4013593 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013594 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term132 A B s f y) = (term132 A B s f y).
Proof. exact (MK_COMB (@lem4013593 A) (@lem4013592 A B s f y)). Qed.
Lemma lem4013615 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : B -> A) (y : B) : (term239 A B s f x' y) = (term239 A B s f x' y).
Proof. exact (eq_refl (term239 A B s f x' y)). Qed.
Lemma lem4013616 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term240 A B x' s f y) = (term240 A B x' s f y).
Proof. exact (MK_COMB (@lem4013615 A B s f x' y) (@lem4013594 A B s f y)). Qed.
Lemma lem4013625 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4013626 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term185 A B t x' s f y) = (term185 A B t x' s f y).
Proof. exact (MK_COMB (@lem4013625 B y t) (@lem4013616 A B x' s f y)). Qed.
Lemma lem4013627 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) : (term187 A B t x' s f) = (term187 A B t x' s f).
Proof. exact (fun_ext (fun y : B => @lem4013626 A B t x' s f y)). Qed.
Lemma lem4013628 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4013629 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) : (term189 A B t x' s f) = (term189 A B t x' s f).
Proof. exact (MK_COMB (@lem4013628 B) (@lem4013627 A B t x' s f)). Qed.
Lemma lem4013630 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x' s f) : term189 A B t x' s f.
Proof. exact (EQ_MP (@lem4013629 A B t x' s f) (@lem4013470 A B t x' s f h1)). Qed.
Lemma lem4013631 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : term423 A B s f x y.
Proof. exact (h1). Qed.
Lemma lem4013634 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : term424 A B s x f y.
Proof. exact (proj1 (@lem4013631 A B s f x y h1)). Qed.
Lemma lem4013635 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : term480 A B s x f y.
Proof. exact (proj2 (@lem4013634 A B s f x y h1)). Qed.
Lemma lem4013650 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term82 A B s f x t) = (term82 A B s f x t).
Proof. exact (eq_refl (term82 A B s f x t)). Qed.
Lemma lem4013651 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term84 A B s f t) = (term84 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem4013650 A B s f x t)). Qed.
Lemma lem4013652 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013654 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term85 A B s f t) = (term85 A B s f t).
Proof. exact (MK_COMB (@lem4013652 A) (@lem4013651 A B s f t)). Qed.
Lemma lem4013655 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term85 A B s f t.
Proof. exact (EQ_MP (@lem4013654 A B s f t) (@lem4013495 A B s f t h1)). Qed.
Lemma lem4013657 {A : Type'} (P : Prop) (Q : A -> Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4013658 {A : Type'} (P : Prop) (Q : A -> Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (@lem4013657 A P Q). Qed.
Lemma lem4013659 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term120 A B s f y x) = (term119 A B s f y x).
Proof. exact (@lem4013658 A (term87 A B s f x y) (term121 A B s f y x)). Qed.
Lemma lem4013660 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term122 A B s f y x x') = (term95 A B s f y x' x).
Proof. exact (eq_refl (term122 A B s f y x x')). Qed.
Lemma lem4013661 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term127 A B s f y x) = (term121 A B s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4013660 A B s f y x' x)). Qed.
Lemma lem4013662 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013663 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term128 A B s f y x) = (term129 A B s f y x).
Proof. exact (MK_COMB (@lem4013662 A) (@lem4013661 A B s f y x)). Qed.
Lemma lem4013664 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term93 A B s f x y) = (term93 A B s f x y).
Proof. exact (eq_refl (term93 A B s f x y)). Qed.
Lemma lem4013665 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term120 A B s f y x) = (term130 A B s f y x).
Proof. exact (MK_COMB (@lem4013664 A B s f x y) (@lem4013663 A B s f y x)). Qed.
Lemma lem4013666 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4013667 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term241 A B s f y x) = (term242 A B s f y x).
Proof. exact (MK_COMB (@lem4013666) (@lem4013665 A B s f y x)). Qed.
Lemma lem4013668 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term122 A B s f y x x') = (term95 A B s f y x' x).
Proof. exact (eq_refl (term122 A B s f y x x')). Qed.
Lemma lem4013669 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term93 A B s f x y) = (term93 A B s f x y).
Proof. exact (eq_refl (term93 A B s f x y)). Qed.
Lemma lem4013670 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term123 A B s f y x x') = (term97 A B s f y x' x).
Proof. exact (MK_COMB (@lem4013669 A B s f x y) (@lem4013668 A B s f y x' x)). Qed.
Lemma lem4013671 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term124 A B s f y x) = (term99 A B s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4013670 A B s f y x' x)). Qed.
Lemma lem4013672 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013673 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term119 A B s f y x) = (term101 A B s f y x).
Proof. exact (MK_COMB (@lem4013672 A) (@lem4013671 A B s f y x)). Qed.
Lemma lem4013674 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : ((term120 A B s f y x) = (term119 A B s f y x)) = ((term130 A B s f y x) = (term101 A B s f y x)).
Proof. exact (MK_COMB (@lem4013667 A B s f y x) (@lem4013673 A B s f y x)). Qed.
Lemma lem4013675 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term130 A B s f y x) = (term101 A B s f y x).
Proof. exact (EQ_MP (@lem4013674 A B s f y x) (@lem4013659 A B s f y x)). Qed.
Lemma lem4013676 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term131 A B s f y) = (term103 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4013675 A B s f y x)). Qed.
Lemma lem4013677 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013678 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term132 A B s f y) = (term105 A B s f y).
Proof. exact (MK_COMB (@lem4013677 A) (@lem4013676 A B s f y)). Qed.
Lemma lem4013679 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : B -> A) (y : B) : (term239 A B s f x' y) = (term239 A B s f x' y).
Proof. exact (eq_refl (term239 A B s f x' y)). Qed.
Lemma lem4013680 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term240 A B x' s f y) = (term243 A B x' s f y).
Proof. exact (MK_COMB (@lem4013679 A B s f x' y) (@lem4013678 A B s f y)). Qed.
Lemma lem4013682 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4013683 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (@lem4013682 A P Q). Qed.
Lemma lem4013684 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term246 A B x' s f y) = (term247 A B x' s f y).
Proof. exact (@lem4013683 A (term248 A B s f x' y) (term103 A B s f y)). Qed.
Lemma lem4013685 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term249 A B s f y x) = (term101 A B s f y x).
Proof. exact (eq_refl (term249 A B s f y x)). Qed.
Lemma lem4013686 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term250 A B s f y) = (term103 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4013685 A B s f y x)). Qed.
Lemma lem4013687 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013688 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term251 A B s f y) = (term105 A B s f y).
Proof. exact (MK_COMB (@lem4013687 A) (@lem4013686 A B s f y)). Qed.
Lemma lem4013689 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : B -> A) (y : B) : (term239 A B s f x' y) = (term239 A B s f x' y).
Proof. exact (eq_refl (term239 A B s f x' y)). Qed.
Lemma lem4013690 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term246 A B x' s f y) = (term243 A B x' s f y).
Proof. exact (MK_COMB (@lem4013689 A B s f x' y) (@lem4013688 A B s f y)). Qed.
Lemma lem4013691 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4013692 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term252 A B x' s f y) = (term253 A B x' s f y).
Proof. exact (MK_COMB (@lem4013691) (@lem4013690 A B x' s f y)). Qed.
Lemma lem4013693 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term249 A B s f y x) = (term101 A B s f y x).
Proof. exact (eq_refl (term249 A B s f y x)). Qed.
Lemma lem4013694 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : B -> A) (y : B) : (term239 A B s f x' y) = (term239 A B s f x' y).
Proof. exact (eq_refl (term239 A B s f x' y)). Qed.
Lemma lem4013695 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term254 A B x' s f y x) = (term255 A B x' s f y x).
Proof. exact (MK_COMB (@lem4013694 A B s f x' y) (@lem4013693 A B s f y x)). Qed.
Lemma lem4013696 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term256 A B x' s f y) = (term257 A B x' s f y).
Proof. exact (fun_ext (fun x : A => @lem4013695 A B x' s f y x)). Qed.
Lemma lem4013697 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013698 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term247 A B x' s f y) = (term258 A B x' s f y).
Proof. exact (MK_COMB (@lem4013697 A) (@lem4013696 A B x' s f y)). Qed.
Lemma lem4013699 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : ((term246 A B x' s f y) = (term247 A B x' s f y)) = ((term243 A B x' s f y) = (term258 A B x' s f y)).
Proof. exact (MK_COMB (@lem4013692 A B x' s f y) (@lem4013698 A B x' s f y)). Qed.
Lemma lem4013700 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term243 A B x' s f y) = (term258 A B x' s f y).
Proof. exact (EQ_MP (@lem4013699 A B x' s f y) (@lem4013684 A B x' s f y)). Qed.
Lemma lem4013702 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4013703 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (@lem4013702 A P Q). Qed.
Lemma lem4013704 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term259 A B x' s f y x) = (term260 A B x' s f y x).
Proof. exact (@lem4013703 A (term248 A B s f x' y) (term99 A B s f y x)). Qed.
Lemma lem4013705 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term261 A B s f y x x') = (term97 A B s f y x' x).
Proof. exact (eq_refl (term261 A B s f y x x')). Qed.
Lemma lem4013706 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term262 A B s f y x) = (term99 A B s f y x).
Proof. exact (fun_ext (fun x' : A => @lem4013705 A B s f y x' x)). Qed.
Lemma lem4013707 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013708 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term263 A B s f y x) = (term101 A B s f y x).
Proof. exact (MK_COMB (@lem4013707 A) (@lem4013706 A B s f y x)). Qed.
Lemma lem4013709 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : B -> A) (y : B) : (term239 A B s f x' y) = (term239 A B s f x' y).
Proof. exact (eq_refl (term239 A B s f x' y)). Qed.
Lemma lem4013710 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term259 A B x' s f y x) = (term255 A B x' s f y x).
Proof. exact (MK_COMB (@lem4013709 A B s f x' y) (@lem4013708 A B s f y x)). Qed.
Lemma lem4013711 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4013712 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term264 A B x' s f y x) = (term265 A B x' s f y x).
Proof. exact (MK_COMB (@lem4013711) (@lem4013710 A B x' s f y x)). Qed.
Lemma lem4013713 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term261 A B s f y x x') = (term97 A B s f y x' x).
Proof. exact (eq_refl (term261 A B s f y x x')). Qed.
Lemma lem4013714 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : B -> A) (y : B) : (term239 A B s f x' y) = (term239 A B s f x' y).
Proof. exact (eq_refl (term239 A B s f x' y)). Qed.
Lemma lem4013715 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x'' : A) (x : A) : (term266 A B x' s f y x x'') = (term267 A B x' s f y x'' x).
Proof. exact (MK_COMB (@lem4013714 A B s f x' y) (@lem4013713 A B s f y x'' x)). Qed.
Lemma lem4013716 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term268 A B x' s f y x) = (term269 A B x' s f y x).
Proof. exact (fun_ext (fun x'' : A => @lem4013715 A B x' s f y x'' x)). Qed.
Lemma lem4013717 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013718 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term260 A B x' s f y x) = (term270 A B x' s f y x).
Proof. exact (MK_COMB (@lem4013717 A) (@lem4013716 A B x' s f y x)). Qed.
Lemma lem4013719 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : ((term259 A B x' s f y x) = (term260 A B x' s f y x)) = ((term255 A B x' s f y x) = (term270 A B x' s f y x)).
Proof. exact (MK_COMB (@lem4013712 A B x' s f y x) (@lem4013718 A B x' s f y x)). Qed.
Lemma lem4013720 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term255 A B x' s f y x) = (term270 A B x' s f y x).
Proof. exact (EQ_MP (@lem4013719 A B x' s f y x) (@lem4013704 A B x' s f y x)). Qed.
Lemma lem4013721 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term257 A B x' s f y) = (term271 A B x' s f y).
Proof. exact (fun_ext (fun x : A => @lem4013720 A B x' s f y x)). Qed.
Lemma lem4013722 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013723 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term258 A B x' s f y) = (term272 A B x' s f y).
Proof. exact (MK_COMB (@lem4013722 A) (@lem4013721 A B x' s f y)). Qed.
Lemma lem4013724 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term243 A B x' s f y) = (term272 A B x' s f y).
Proof. exact (TRANS (@lem4013700 A B x' s f y) (@lem4013723 A B x' s f y)). Qed.
Lemma lem4013725 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term240 A B x' s f y) = (term272 A B x' s f y).
Proof. exact (TRANS (@lem4013680 A B x' s f y) (@lem4013724 A B x' s f y)). Qed.
Lemma lem4013726 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4013727 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term185 A B t x' s f y) = (term273 A B t x' s f y).
Proof. exact (MK_COMB (@lem4013726 B y t) (@lem4013725 A B x' s f y)). Qed.
Lemma lem4013729 {A : Type'} (P : Prop) (Q : A -> Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4013730 {A : Type'} (P : Prop) (Q : A -> Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (@lem4013729 A P Q). Qed.
Lemma lem4013731 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term274 A B t x' s f y) = (term275 A B t x' s f y).
Proof. exact (@lem4013730 A (term155 B y t) (term271 A B x' s f y)). Qed.
Lemma lem4013732 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term276 A B x' s f y x) = (term270 A B x' s f y x).
Proof. exact (eq_refl (term276 A B x' s f y x)). Qed.
Lemma lem4013733 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term277 A B x' s f y) = (term271 A B x' s f y).
Proof. exact (fun_ext (fun x : A => @lem4013732 A B x' s f y x)). Qed.
Lemma lem4013734 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013735 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term278 A B x' s f y) = (term272 A B x' s f y).
Proof. exact (MK_COMB (@lem4013734 A) (@lem4013733 A B x' s f y)). Qed.
Lemma lem4013736 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4013737 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term274 A B t x' s f y) = (term273 A B t x' s f y).
Proof. exact (MK_COMB (@lem4013736 B y t) (@lem4013735 A B x' s f y)). Qed.
Lemma lem4013738 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4013739 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term279 A B t x' s f y) = (term280 A B t x' s f y).
Proof. exact (MK_COMB (@lem4013738) (@lem4013737 A B t x' s f y)). Qed.
Lemma lem4013740 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term276 A B x' s f y x) = (term270 A B x' s f y x).
Proof. exact (eq_refl (term276 A B x' s f y x)). Qed.
Lemma lem4013741 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4013742 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term281 A B t x' s f y x) = (term282 A B t x' s f y x).
Proof. exact (MK_COMB (@lem4013741 B y t) (@lem4013740 A B x' s f y x)). Qed.
Lemma lem4013743 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term283 A B t x' s f y) = (term284 A B t x' s f y).
Proof. exact (fun_ext (fun x : A => @lem4013742 A B t x' s f y x)). Qed.
Lemma lem4013744 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013745 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term275 A B t x' s f y) = (term285 A B t x' s f y).
Proof. exact (MK_COMB (@lem4013744 A) (@lem4013743 A B t x' s f y)). Qed.
Lemma lem4013746 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : ((term274 A B t x' s f y) = (term275 A B t x' s f y)) = ((term273 A B t x' s f y) = (term285 A B t x' s f y)).
Proof. exact (MK_COMB (@lem4013739 A B t x' s f y) (@lem4013745 A B t x' s f y)). Qed.
Lemma lem4013747 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term273 A B t x' s f y) = (term285 A B t x' s f y).
Proof. exact (EQ_MP (@lem4013746 A B t x' s f y) (@lem4013731 A B t x' s f y)). Qed.
Lemma lem4013749 {A : Type'} (P : Prop) (Q : A -> Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4013750 {A : Type'} (P : Prop) (Q : A -> Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (@lem4013749 A P Q). Qed.
Lemma lem4013751 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term286 A B t x' s f y x) = (term287 A B t x' s f y x).
Proof. exact (@lem4013750 A (term155 B y t) (term269 A B x' s f y x)). Qed.
Lemma lem4013752 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x'' : A) (x : A) : (term288 A B x' s f y x x'') = (term267 A B x' s f y x'' x).
Proof. exact (eq_refl (term288 A B x' s f y x x'')). Qed.
Lemma lem4013753 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term289 A B x' s f y x) = (term269 A B x' s f y x).
Proof. exact (fun_ext (fun x'' : A => @lem4013752 A B x' s f y x'' x)). Qed.
Lemma lem4013754 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013755 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term290 A B x' s f y x) = (term270 A B x' s f y x).
Proof. exact (MK_COMB (@lem4013754 A) (@lem4013753 A B x' s f y x)). Qed.
Lemma lem4013756 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4013757 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term286 A B t x' s f y x) = (term282 A B t x' s f y x).
Proof. exact (MK_COMB (@lem4013756 B y t) (@lem4013755 A B x' s f y x)). Qed.
Lemma lem4013758 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4013759 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term291 A B t x' s f y x) = (term292 A B t x' s f y x).
Proof. exact (MK_COMB (@lem4013758) (@lem4013757 A B t x' s f y x)). Qed.
Lemma lem4013760 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x'' : A) (x : A) : (term288 A B x' s f y x x'') = (term267 A B x' s f y x'' x).
Proof. exact (eq_refl (term288 A B x' s f y x x'')). Qed.
Lemma lem4013761 {B : Type'} (y : B) (t : B -> Prop) : (term112 B y t) = (term112 B y t).
Proof. exact (eq_refl (term112 B y t)). Qed.
Lemma lem4013762 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x'' : A) (x : A) : (term293 A B t x' s f y x x'') = (term294 A B t x' s f y x'' x).
Proof. exact (MK_COMB (@lem4013761 B y t) (@lem4013760 A B x' s f y x'' x)). Qed.
Lemma lem4013763 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term295 A B t x' s f y x) = (term296 A B t x' s f y x).
Proof. exact (fun_ext (fun x'' : A => @lem4013762 A B t x' s f y x'' x)). Qed.
Lemma lem4013764 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013765 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term287 A B t x' s f y x) = (term297 A B t x' s f y x).
Proof. exact (MK_COMB (@lem4013764 A) (@lem4013763 A B t x' s f y x)). Qed.
Lemma lem4013766 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : ((term286 A B t x' s f y x) = (term287 A B t x' s f y x)) = ((term282 A B t x' s f y x) = (term297 A B t x' s f y x)).
Proof. exact (MK_COMB (@lem4013759 A B t x' s f y x) (@lem4013765 A B t x' s f y x)). Qed.
Lemma lem4013767 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term282 A B t x' s f y x) = (term297 A B t x' s f y x).
Proof. exact (EQ_MP (@lem4013766 A B t x' s f y x) (@lem4013751 A B t x' s f y x)). Qed.
Lemma lem4013768 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term284 A B t x' s f y) = (term298 A B t x' s f y).
Proof. exact (fun_ext (fun x : A => @lem4013767 A B t x' s f y x)). Qed.
Lemma lem4013769 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013770 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term285 A B t x' s f y) = (term299 A B t x' s f y).
Proof. exact (MK_COMB (@lem4013769 A) (@lem4013768 A B t x' s f y)). Qed.
Lemma lem4013771 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term273 A B t x' s f y) = (term299 A B t x' s f y).
Proof. exact (TRANS (@lem4013747 A B t x' s f y) (@lem4013770 A B t x' s f y)). Qed.
Lemma lem4013772 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (y : B) : (term185 A B t x' s f y) = (term299 A B t x' s f y).
Proof. exact (TRANS (@lem4013727 A B t x' s f y) (@lem4013771 A B t x' s f y)). Qed.
Lemma lem4013773 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) : (term187 A B t x' s f) = (term300 A B t x' s f).
Proof. exact (fun_ext (fun y : B => @lem4013772 A B t x' s f y)). Qed.
Lemma lem4013774 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4013775 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) : (term189 A B t x' s f) = (term301 A B t x' s f).
Proof. exact (MK_COMB (@lem4013774 B) (@lem4013773 A B t x' s f)). Qed.
Lemma lem4013813 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (x'' : A) (x : A) : (term294 A B t x' s f y x'' x) = (term302 A B x' t s f y x'' x).
Proof. exact (@lem19490 (term248 A B s f x' y) (term155 B y t) (term97 A B s f y x'' x)). Qed.
Lemma lem4013814 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (x : A) : (term303 A B t s f y x' x) = (term303 A B t s f y x' x).
Proof. exact (eq_refl (term303 A B t s f y x' x)). Qed.
Lemma lem4013821 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : B -> A) (y : B) : (term304 A B t s f x' y) = (term305 A B s t f x' y).
Proof. exact (@lem19490 (term306 A B x' y s) (term155 B y t) ((term307 A B f x' y) = y)). Qed.
Lemma lem4013822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4013823 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : B -> A) (y : B) : (term308 A B t s f x' y) = (term309 A B s t f x' y).
Proof. exact (MK_COMB (@lem4013822) (@lem4013821 A B s t f x' y)). Qed.
Lemma lem4013824 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (x'' : A) (x : A) : (term302 A B x' t s f y x'' x) = (term310 A B x' t s f y x'' x).
Proof. exact (MK_COMB (@lem4013823 A B s t f x' y) (@lem4013814 A B t s f y x'' x)). Qed.
Lemma lem4013826 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (x'' : A) (x : A) : (term294 A B t x' s f y x'' x) = (term310 A B x' t s f y x'' x).
Proof. exact (TRANS (@lem4013813 A B x' t s f y x'' x) (@lem4013824 A B x' t s f y x'' x)). Qed.
Lemma lem4013827 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term296 A B t x' s f y x) = (term311 A B x' t s f y x).
Proof. exact (fun_ext (fun x'' : A => @lem4013826 A B x' t s f y x'' x)). Qed.
Lemma lem4013828 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013829 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term297 A B t x' s f y x) = (term312 A B x' t s f y x).
Proof. exact (MK_COMB (@lem4013828 A) (@lem4013827 A B x' t s f y x)). Qed.
Lemma lem4013830 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term298 A B t x' s f y) = (term313 A B x' t s f y).
Proof. exact (fun_ext (fun x : A => @lem4013829 A B x' t s f y x)). Qed.
Lemma lem4013831 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4013832 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term299 A B t x' s f y) = (term314 A B x' t s f y).
Proof. exact (MK_COMB (@lem4013831 A) (@lem4013830 A B x' t s f y)). Qed.
Lemma lem4013833 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term300 A B t x' s f) = (term315 A B x' t s f).
Proof. exact (fun_ext (fun y : B => @lem4013832 A B x' t s f y)). Qed.
Lemma lem4013834 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4013835 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term301 A B t x' s f) = (term316 A B x' t s f).
Proof. exact (MK_COMB (@lem4013834 B) (@lem4013833 A B x' t s f)). Qed.
Lemma lem4013836 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term189 A B t x' s f) = (term316 A B x' t s f).
Proof. exact (TRANS (@lem4013775 A B t x' s f) (@lem4013835 A B x' t s f)). Qed.
Lemma lem4013837 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x' s f) : term316 A B x' t s f.
Proof. exact (EQ_MP (@lem4013836 A B x' t s f) (@lem4013630 A B t x' s f h1)). Qed.
Lemma lem4013857 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4014056 {A : Type'} (s : A -> Prop) (h1 : term441 A s) : term441 A s.
Proof. exact (h1). Qed.
Lemma lem4014057 {A B : Type'} (_46355 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term321 A B s f t _46355.
Proof. exact (@lem4013655 A B s f t h1 _46355). Qed.
Lemma lem4014058 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46355 : A) (t : B -> Prop) : (term321 A B s f t _46355) = (term82 A B s f _46355 t).
Proof. exact (eq_refl (term321 A B s f t _46355)). Qed.
Lemma lem4014060 {A B : Type'} (_46356 : B) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x' s f) : term317 A B x' t s f _46356.
Proof. exact (@lem4013837 A B t x' s f h1 _46356). Qed.
Lemma lem4014061 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (_46356 : B) : (term317 A B x' t s f _46356) = (term314 A B x' t s f _46356).
Proof. exact (eq_refl (term317 A B x' t s f _46356)). Qed.
Lemma lem4014062 {A B : Type'} (_46356 : B) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x' s f) : term314 A B x' t s f _46356.
Proof. exact (EQ_MP (@lem4014061 A B x' t s f _46356) (@lem4014060 A B _46356 t x' s f h1)). Qed.
Lemma lem4014063 {A B : Type'} (_46356 : B) (_46357 : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x' s f) : term318 A B x' t s f _46356 _46357.
Proof. exact (@lem4014062 A B _46356 t x' s f h1 _46357). Qed.
Lemma lem4014064 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (_46356 : B) (_46357 : A) : (term318 A B x' t s f _46356 _46357) = (term312 A B x' t s f _46356 _46357).
Proof. exact (eq_refl (term318 A B x' t s f _46356 _46357)). Qed.
Lemma lem4014065 {A B : Type'} (_46356 : B) (_46357 : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x' s f) : term312 A B x' t s f _46356 _46357.
Proof. exact (EQ_MP (@lem4014064 A B x' t s f _46356 _46357) (@lem4014063 A B _46356 _46357 t x' s f h1)). Qed.
Lemma lem4014066 {A B : Type'} (_46356 : B) (_46357 : A) (_46358 : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x' s f) : term319 A B x' t s f _46356 _46357 _46358.
Proof. exact (@lem4014065 A B _46356 _46357 t x' s f h1 _46358). Qed.
Lemma lem4014067 {A B : Type'} (x' : B -> A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (_46356 : B) (_46358 : A) (_46357 : A) : (term319 A B x' t s f _46356 _46357 _46358) = (term310 A B x' t s f _46356 _46358 _46357).
Proof. exact (eq_refl (term319 A B x' t s f _46356 _46357 _46358)). Qed.
Lemma lem4014068 {A B : Type'} (_46356 : B) (_46358 : A) (_46357 : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x' s f) : term310 A B x' t s f _46356 _46358 _46357.
Proof. exact (EQ_MP (@lem4014067 A B x' t s f _46356 _46358 _46357) (@lem4014066 A B _46356 _46357 _46358 t x' s f h1)). Qed.
Lemma lem4014081 {A B : Type'} (_46356 : B) (_46358 : A) (_46357 : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x' s f) : term303 A B t s f _46356 _46358 _46357.
Proof. exact (proj2 (@lem4014068 A B _46356 _46358 _46357 t x' s f h1)). Qed.
Lemma lem4014096 {A B : Type'} (_46355 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term82 A B s f _46355 t.
Proof. exact (EQ_MP (@lem4014058 A B s f _46355 t) (@lem4014057 A B _46355 s f t h1)). Qed.
Lemma lem4014098 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : term347 A x y.
Proof. exact (proj2 (@lem4013631 A B s f x y h1)). Qed.
Lemma lem4014115 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46356 : B) (_46358 : A) (_46357 : A) : (term95 A B s f _46356 _46358 _46357) = (term481 A B s f _46356 _46358 _46357).
Proof. exact (@lem4010111 (term155 A _46358 s) (term482 A B f _46358 _46356) (_46358 = _46357)). Qed.
Lemma lem4014116 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46357 : A) (_46356 : B) : (term93 A B s f _46357 _46356) = (term93 A B s f _46357 _46356).
Proof. exact (eq_refl (term93 A B s f _46357 _46356)). Qed.
Lemma lem4014117 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46356 : B) (_46358 : A) (_46357 : A) : (term97 A B s f _46356 _46358 _46357) = (term483 A B s f _46356 _46358 _46357).
Proof. exact (MK_COMB (@lem4014116 A B s f _46357 _46356) (@lem4014115 A B s f _46356 _46358 _46357)). Qed.
Lemma lem4014124 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46356 : B) (_46358 : A) (_46357 : A) : (term483 A B s f _46356 _46358 _46357) = (term484 A B s f _46356 _46358 _46357).
Proof. exact (@lem4010111 (term155 A _46357 s) (term482 A B f _46357 _46356) (term481 A B s f _46356 _46358 _46357)). Qed.
Lemma lem4014125 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46356 : B) (_46358 : A) (_46357 : A) : (term97 A B s f _46356 _46358 _46357) = (term484 A B s f _46356 _46358 _46357).
Proof. exact (TRANS (@lem4014117 A B s f _46356 _46358 _46357) (@lem4014124 A B s f _46356 _46358 _46357)). Qed.
Lemma lem4014126 {B : Type'} (_46356 : B) (t : B -> Prop) : (term112 B _46356 t) = (term112 B _46356 t).
Proof. exact (eq_refl (term112 B _46356 t)). Qed.
Lemma lem4014129 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (_46356 : B) (_46358 : A) (_46357 : A) : (term303 A B t s f _46356 _46358 _46357) = (term485 A B t s f _46356 _46358 _46357).
Proof. exact (MK_COMB (@lem4014126 B _46356 t) (@lem4014125 A B s f _46356 _46358 _46357)). Qed.
Lemma lem4014130 {A B : Type'} (_46356 : B) (_46358 : A) (_46357 : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x' s f) : term485 A B t s f _46356 _46358 _46357.
Proof. exact (EQ_MP (@lem4014129 A B t s f _46356 _46358 _46357) (@lem4014081 A B _46356 _46358 _46357 t x' s f h1)). Qed.
Lemma lem4014144 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4014152 {A : Type'} (s : A -> Prop) (h1 : term441 A s) : term441 A s.
Proof. exact (h1). Qed.
Lemma lem4014266 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : @IN A y s.
Proof. exact (proj1 (@lem4013635 A B s f x y h1)). Qed.
Lemma lem4014267 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : term331 A y s.
Proof. exact (fun h0 : term155 A y s => @lem4014266 A B s f x y h1). Qed.
Lemma lem4014269 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4014270 {A : Type'} (y : A) (s : A -> Prop) : (term331 A y s) = (@IN A y s).
Proof. exact (@lem4014269 (@IN A y s)). Qed.
Lemma lem4014271 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : @IN A y s.
Proof. exact (EQ_MP (@lem4014270 A y s) (@lem4014267 A B s f x y h1)). Qed.
Lemma lem4014277 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4014278 {A B : Type'} (f : A -> B) (t : B -> Prop) (_46355 : A) (s : A -> Prop) : (term82 A B s f _46355 t) = (term383 A B f t _46355 s).
Proof. exact (@lem4014277 (term83 A B f _46355 t) (term155 A _46355 s)). Qed.
Lemma lem4014284 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4014285 {A B : Type'} (f : A -> B) (t : B -> Prop) (_46355 : A) (s : A -> Prop) : (term384 A B s f _46355 t) = (term385 A B f t _46355 s).
Proof. exact (MK_COMB (@lem4014284) (@lem4014278 A B f t _46355 s)). Qed.
Lemma lem4014291 {A B : Type'} (f : A -> B) (t : B -> Prop) (_46355 : A) (s : A -> Prop) : (term383 A B f t _46355 s) = (term383 A B f t _46355 s).
Proof. exact (eq_refl (term383 A B f t _46355 s)). Qed.
Lemma lem4014292 {A B : Type'} (f : A -> B) (t : B -> Prop) (_46355 : A) (s : A -> Prop) : ((term82 A B s f _46355 t) = (term383 A B f t _46355 s)) = ((term383 A B f t _46355 s) = (term383 A B f t _46355 s)).
Proof. exact (MK_COMB (@lem4014285 A B f t _46355 s) (@lem4014291 A B f t _46355 s)). Qed.
Lemma lem4014294 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4014295 (x : Prop) : (x = x) = True.
Proof. exact (@lem4014294 Prop x). Qed.
Lemma lem4014296 {A B : Type'} (f : A -> B) (t : B -> Prop) (_46355 : A) (s : A -> Prop) : ((term383 A B f t _46355 s) = (term383 A B f t _46355 s)) = True.
Proof. exact (@lem4014295 (term383 A B f t _46355 s)). Qed.
Lemma lem4014297 {A B : Type'} (f : A -> B) (t : B -> Prop) (_46355 : A) (s : A -> Prop) : ((term82 A B s f _46355 t) = (term383 A B f t _46355 s)) = True.
Proof. exact (TRANS (@lem4014292 A B f t _46355 s) (@lem4014296 A B f t _46355 s)). Qed.
Lemma lem4014298 {A B : Type'} (f : A -> B) (t : B -> Prop) (_46355 : A) (s : A -> Prop) : True = ((term82 A B s f _46355 t) = (term383 A B f t _46355 s)).
Proof. exact (SYM (@lem4014297 A B f t _46355 s)). Qed.
Lemma lem4014299 {A B : Type'} (f : A -> B) (t : B -> Prop) (_46355 : A) (s : A -> Prop) : (term82 A B s f _46355 t) = (term383 A B f t _46355 s).
Proof. exact (EQ_MP (@lem4014298 A B f t _46355 s) (@lem0)). Qed.
Lemma lem4014300 {A B : Type'} (_46355 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term383 A B f t _46355 s.
Proof. exact (EQ_MP (@lem4014299 A B f t _46355 s) (@lem4014096 A B _46355 s f t h1)). Qed.
Lemma lem4014302 (b : Prop) (a : Prop) : (a \/ b) = (term336 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4014303 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46355 : A) (t : B -> Prop) : (term383 A B f t _46355 s) = (term386 A B s f _46355 t).
Proof. exact (@lem4014302 (term155 A _46355 s) (term83 A B f _46355 t)). Qed.
Lemma lem4014305 (a : Prop) : (term49 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4014306 {A : Type'} (_46355 : A) (s : A -> Prop) : (term338 A _46355 s) = (@IN A _46355 s).
Proof. exact (@lem4014305 (@IN A _46355 s)). Qed.
Lemma lem4014307 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4014308 {A : Type'} (_46355 : A) (s : A -> Prop) : (term339 A _46355 s) = (term75 A _46355 s).
Proof. exact (MK_COMB (@lem4014307) (@lem4014306 A _46355 s)). Qed.
Lemma lem4014309 {A B : Type'} (f : A -> B) (_46355 : A) (t : B -> Prop) : (term83 A B f _46355 t) = (term83 A B f _46355 t).
Proof. exact (eq_refl (term83 A B f _46355 t)). Qed.
Lemma lem4014310 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46355 : A) (t : B -> Prop) : (term386 A B s f _46355 t) = (term78 A B s f _46355 t).
Proof. exact (MK_COMB (@lem4014308 A _46355 s) (@lem4014309 A B f _46355 t)). Qed.
Lemma lem4014311 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46355 : A) (t : B -> Prop) : (term383 A B f t _46355 s) = (term78 A B s f _46355 t).
Proof. exact (TRANS (@lem4014303 A B s f _46355 t) (@lem4014310 A B s f _46355 t)). Qed.
Lemma lem4014314 {A B : Type'} (_46355 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term78 A B s f _46355 t.
Proof. exact (EQ_MP (@lem4014311 A B s f _46355 t) (@lem4014300 A B _46355 s f t h1)). Qed.
Lemma lem4014315 {A B : Type'} (_46355 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term78 A B s f _46355 t.
Proof. exact (@lem4014314 A B _46355 s f t h1). Qed.
Lemma lem4014316 {A B : Type'} (y : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term30 A B s f t) : term78 A B s f y t.
Proof. exact (@lem4014315 A B y s f t h1). Qed.
Lemma lem4014319 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term30 A B s f t) (h2 : term423 A B s f x y) : term83 A B f y t.
Proof. exact (@lem4014316 A B y s f t h1 (@lem4014271 A B s f x y h2)). Qed.
Lemma lem4014320 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term30 A B s f t) (h2 : term423 A B s f x y) : term387 A B f y t.
Proof. exact (fun h0 : term327 A B f y t => @lem4014319 A B t s f x y h1 h2). Qed.
Lemma lem4014322 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4014323 {A B : Type'} (f : A -> B) (y : A) (t : B -> Prop) : (term387 A B f y t) = (term83 A B f y t).
Proof. exact (@lem4014322 (term83 A B f y t)). Qed.
Lemma lem4014324 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term30 A B s f t) (h2 : term423 A B s f x y) : term83 A B f y t.
Proof. exact (EQ_MP (@lem4014323 A B f y t) (@lem4014320 A B t s f x y h1 h2)). Qed.
Lemma lem4014326 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : @IN A y s.
Proof. exact (proj1 (@lem4013635 A B s f x y h1)). Qed.
Lemma lem4014327 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : term331 A y s.
Proof. exact (fun h0 : term155 A y s => @lem4014326 A B s f x y h1). Qed.
Lemma lem4014329 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4014330 {A : Type'} (y : A) (s : A -> Prop) : (term331 A y s) = (@IN A y s).
Proof. exact (@lem4014329 (@IN A y s)). Qed.
Lemma lem4014331 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : @IN A y s.
Proof. exact (EQ_MP (@lem4014330 A y s) (@lem4014327 A B s f x y h1)). Qed.
Lemma lem4014333 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4014334 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4014333 B x). Qed.
Lemma lem4014335 {A B : Type'} (f : A -> B) (y : A) : (f y) = (f y).
Proof. exact (@lem4014334 B (f y)). Qed.
Lemma lem4014336 {A B : Type'} (f : A -> B) (y : A) : term486 A B f y.
Proof. exact (fun h0 : term487 A B f y => @lem4014335 A B f y). Qed.
Lemma lem4014338 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4014339 {A B : Type'} (f : A -> B) (y : A) : (term486 A B f y) = ((f y) = (f y)).
Proof. exact (@lem4014338 ((f y) = (f y))). Qed.
Lemma lem4014340 {A B : Type'} (f : A -> B) (y : A) : (f y) = (f y).
Proof. exact (EQ_MP (@lem4014339 A B f y) (@lem4014336 A B f y)). Qed.
Lemma lem4014342 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : @IN A x s.
Proof. exact (proj1 (@lem4013634 A B s f x y h1)). Qed.
Lemma lem4014343 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : term331 A x s.
Proof. exact (fun h0 : term155 A x s => @lem4014342 A B s f x y h1). Qed.
Lemma lem4014345 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4014346 {A : Type'} (x : A) (s : A -> Prop) : (term331 A x s) = (@IN A x s).
Proof. exact (@lem4014345 (@IN A x s)). Qed.
Lemma lem4014347 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : @IN A x s.
Proof. exact (EQ_MP (@lem4014346 A x s) (@lem4014343 A B s f x y h1)). Qed.
Lemma lem4014349 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : (f x) = (f y).
Proof. exact (proj2 (@lem4013635 A B s f x y h1)). Qed.
Lemma lem4014350 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : term488 A B x f y.
Proof. exact (fun h0 : term489 A B x f y => @lem4014349 A B s f x y h1). Qed.
Lemma lem4014352 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4014353 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term488 A B x f y) = ((f x) = (f y)).
Proof. exact (@lem4014352 ((f x) = (f y))). Qed.
Lemma lem4014354 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : (f x) = (f y).
Proof. exact (EQ_MP (@lem4014353 A B x f y) (@lem4014350 A B s f x y h1)). Qed.
Lemma lem4014360 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4014361 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (_46356 : B) (_46358 : A) (_46357 : A) : (term485 A B t s f _46356 _46358 _46357) = (term490 A B t s f _46356 _46358 _46357).
Proof. exact (@lem4014360 (term155 A _46357 s) (term155 B _46356 t) (term491 A B s f _46356 _46358 _46357)). Qed.
Lemma lem4014375 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4014376 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (_46356 : B) (_46358 : A) (_46357 : A) : (term492 A B t s f _46356 _46358 _46357) = (term493 A B t s f _46356 _46358 _46357).
Proof. exact (@lem4014375 (term482 A B f _46357 _46356) (term155 B _46356 t) (term481 A B s f _46356 _46358 _46357)). Qed.
Lemma lem4014392 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4014393 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_46356 : B) (_46358 : A) (_46357 : A) : (term494 A B t s f _46356 _46358 _46357) = (term495 A B s t f _46356 _46358 _46357).
Proof. exact (@lem4014392 (term155 A _46358 s) (term155 B _46356 t) (term496 A B f _46356 _46358 _46357)). Qed.
Lemma lem4014407 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4014408 {A B : Type'} (f : A -> B) (_46356 : B) (t : B -> Prop) (_46358 : A) (_46357 : A) : (term497 A B t f _46356 _46358 _46357) = (term498 A B f _46356 t _46358 _46357).
Proof. exact (@lem4014407 (term482 A B f _46358 _46356) (term155 B _46356 t) (_46358 = _46357)). Qed.
Lemma lem4014424 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4014425 {A B : Type'} (_46358 : A) (_46357 : A) (_46356 : B) (t : B -> Prop) : (term499 A B _46356 t _46358 _46357) = (term500 A B _46358 _46357 _46356 t).
Proof. exact (@lem4014424 (_46358 = _46357) (term155 B _46356 t)). Qed.
Lemma lem4014433 {A B : Type'} (f : A -> B) (_46358 : A) (_46356 : B) : (term501 A B f _46358 _46356) = (term501 A B f _46358 _46356).
Proof. exact (eq_refl (term501 A B f _46358 _46356)). Qed.
Lemma lem4014434 {A B : Type'} (f : A -> B) (_46358 : A) (_46357 : A) (_46356 : B) (t : B -> Prop) : (term498 A B f _46356 t _46358 _46357) = (term502 A B f _46358 _46357 _46356 t).
Proof. exact (MK_COMB (@lem4014433 A B f _46358 _46356) (@lem4014425 A B _46358 _46357 _46356 t)). Qed.
Lemma lem4014438 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4014439 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (_46356 : B) (t : B -> Prop) : (term502 A B f _46358 _46357 _46356 t) = (term503 A B _46357 f _46358 _46356 t).
Proof. exact (@lem4014438 (_46358 = _46357) (term482 A B f _46358 _46356) (term155 B _46356 t)). Qed.
Lemma lem4014459 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (_46356 : B) (t : B -> Prop) : (term498 A B f _46356 t _46358 _46357) = (term503 A B _46357 f _46358 _46356 t).
Proof. exact (TRANS (@lem4014434 A B f _46358 _46357 _46356 t) (@lem4014439 A B _46357 f _46358 _46356 t)). Qed.
Lemma lem4014460 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (_46356 : B) (t : B -> Prop) : (term497 A B t f _46356 _46358 _46357) = (term503 A B _46357 f _46358 _46356 t).
Proof. exact (TRANS (@lem4014408 A B f _46356 t _46358 _46357) (@lem4014459 A B _46357 f _46358 _46356 t)). Qed.
Lemma lem4014461 {A : Type'} (_46358 : A) (s : A -> Prop) : (term112 A _46358 s) = (term112 A _46358 s).
Proof. exact (eq_refl (term112 A _46358 s)). Qed.
Lemma lem4014462 {A B : Type'} (s : A -> Prop) (_46357 : A) (f : A -> B) (_46358 : A) (_46356 : B) (t : B -> Prop) : (term495 A B s t f _46356 _46358 _46357) = (term504 A B s _46357 f _46358 _46356 t).
Proof. exact (MK_COMB (@lem4014461 A _46358 s) (@lem4014460 A B _46357 f _46358 _46356 t)). Qed.
Lemma lem4014466 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4014467 {A B : Type'} (_46357 : A) (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) (t : B -> Prop) : (term504 A B s _46357 f _46358 _46356 t) = (term505 A B _46357 s f _46358 _46356 t).
Proof. exact (@lem4014466 (_46358 = _46357) (term155 A _46358 s) (term506 A B f _46358 _46356 t)). Qed.
Lemma lem4014483 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4014484 {A B : Type'} (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term507 A B s f _46358 _46356 t) = (term508 A B f _46358 s _46356 t).
Proof. exact (@lem4014483 (term482 A B f _46358 _46356) (term155 A _46358 s) (term155 B _46356 t)). Qed.
Lemma lem4014502 {A : Type'} (_46358 : A) (_46357 : A) : (term509 A _46358 _46357) = (term509 A _46358 _46357).
Proof. exact (eq_refl (term509 A _46358 _46357)). Qed.
Lemma lem4014503 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term505 A B _46357 s f _46358 _46356 t) = (term510 A B _46357 f _46358 s _46356 t).
Proof. exact (MK_COMB (@lem4014502 A _46358 _46357) (@lem4014484 A B f _46358 s _46356 t)). Qed.
Lemma lem4014514 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term504 A B s _46357 f _46358 _46356 t) = (term510 A B _46357 f _46358 s _46356 t).
Proof. exact (TRANS (@lem4014467 A B _46357 s f _46358 _46356 t) (@lem4014503 A B _46357 f _46358 s _46356 t)). Qed.
Lemma lem4014515 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term495 A B s t f _46356 _46358 _46357) = (term510 A B _46357 f _46358 s _46356 t).
Proof. exact (TRANS (@lem4014462 A B s _46357 f _46358 _46356 t) (@lem4014514 A B _46357 f _46358 s _46356 t)). Qed.
Lemma lem4014516 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term494 A B t s f _46356 _46358 _46357) = (term510 A B _46357 f _46358 s _46356 t).
Proof. exact (TRANS (@lem4014393 A B s t f _46356 _46358 _46357) (@lem4014515 A B _46357 f _46358 s _46356 t)). Qed.
Lemma lem4014517 {A B : Type'} (f : A -> B) (_46357 : A) (_46356 : B) : (term501 A B f _46357 _46356) = (term501 A B f _46357 _46356).
Proof. exact (eq_refl (term501 A B f _46357 _46356)). Qed.
Lemma lem4014518 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term493 A B t s f _46356 _46358 _46357) = (term511 A B _46357 f _46358 s _46356 t).
Proof. exact (MK_COMB (@lem4014517 A B f _46357 _46356) (@lem4014516 A B _46357 f _46358 s _46356 t)). Qed.
Lemma lem4014522 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4014523 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term511 A B _46357 f _46358 s _46356 t) = (term512 A B _46357 f _46358 s _46356 t).
Proof. exact (@lem4014522 (_46358 = _46357) (term482 A B f _46357 _46356) (term508 A B f _46358 s _46356 t)). Qed.
Lemma lem4014565 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term493 A B t s f _46356 _46358 _46357) = (term512 A B _46357 f _46358 s _46356 t).
Proof. exact (TRANS (@lem4014518 A B _46357 f _46358 s _46356 t) (@lem4014523 A B _46357 f _46358 s _46356 t)). Qed.
Lemma lem4014566 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term492 A B t s f _46356 _46358 _46357) = (term512 A B _46357 f _46358 s _46356 t).
Proof. exact (TRANS (@lem4014376 A B t s f _46356 _46358 _46357) (@lem4014565 A B _46357 f _46358 s _46356 t)). Qed.
Lemma lem4014567 {A : Type'} (_46357 : A) (s : A -> Prop) : (term112 A _46357 s) = (term112 A _46357 s).
Proof. exact (eq_refl (term112 A _46357 s)). Qed.
Lemma lem4014568 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term490 A B t s f _46356 _46358 _46357) = (term513 A B _46357 f _46358 s _46356 t).
Proof. exact (MK_COMB (@lem4014567 A _46357 s) (@lem4014566 A B _46357 f _46358 s _46356 t)). Qed.
Lemma lem4014572 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4014573 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term513 A B _46357 f _46358 s _46356 t) = (term514 A B _46357 f _46358 s _46356 t).
Proof. exact (@lem4014572 (_46358 = _46357) (term155 A _46357 s) (term515 A B _46357 f _46358 s _46356 t)). Qed.
Lemma lem4014589 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4014590 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term516 A B _46357 f _46358 s _46356 t) = (term517 A B _46357 f _46358 s _46356 t).
Proof. exact (@lem4014589 (term482 A B f _46357 _46356) (term155 A _46357 s) (term508 A B f _46358 s _46356 t)). Qed.
Lemma lem4014606 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4014607 {A B : Type'} (f : A -> B) (_46357 : A) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term518 A B _46357 f _46358 s _46356 t) = (term519 A B f _46357 _46358 s _46356 t).
Proof. exact (@lem4014606 (term482 A B f _46358 _46356) (term155 A _46357 s) (term520 A B _46358 s _46356 t)). Qed.
Lemma lem4014635 {A B : Type'} (f : A -> B) (_46357 : A) (_46356 : B) : (term501 A B f _46357 _46356) = (term501 A B f _46357 _46356).
Proof. exact (eq_refl (term501 A B f _46357 _46356)). Qed.
Lemma lem4014636 {A B : Type'} (f : A -> B) (_46357 : A) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term517 A B _46357 f _46358 s _46356 t) = (term521 A B f _46357 _46358 s _46356 t).
Proof. exact (MK_COMB (@lem4014635 A B f _46357 _46356) (@lem4014607 A B f _46357 _46358 s _46356 t)). Qed.
Lemma lem4014647 {A B : Type'} (f : A -> B) (_46357 : A) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term516 A B _46357 f _46358 s _46356 t) = (term521 A B f _46357 _46358 s _46356 t).
Proof. exact (TRANS (@lem4014590 A B _46357 f _46358 s _46356 t) (@lem4014636 A B f _46357 _46358 s _46356 t)). Qed.
Lemma lem4014648 {A : Type'} (_46358 : A) (_46357 : A) : (term509 A _46358 _46357) = (term509 A _46358 _46357).
Proof. exact (eq_refl (term509 A _46358 _46357)). Qed.
Lemma lem4014649 {A B : Type'} (f : A -> B) (_46357 : A) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term514 A B _46357 f _46358 s _46356 t) = (term522 A B f _46357 _46358 s _46356 t).
Proof. exact (MK_COMB (@lem4014648 A _46358 _46357) (@lem4014647 A B f _46357 _46358 s _46356 t)). Qed.
Lemma lem4014660 {A B : Type'} (f : A -> B) (_46357 : A) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term513 A B _46357 f _46358 s _46356 t) = (term522 A B f _46357 _46358 s _46356 t).
Proof. exact (TRANS (@lem4014573 A B _46357 f _46358 s _46356 t) (@lem4014649 A B f _46357 _46358 s _46356 t)). Qed.
Lemma lem4014661 {A B : Type'} (f : A -> B) (_46357 : A) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term490 A B t s f _46356 _46358 _46357) = (term522 A B f _46357 _46358 s _46356 t).
Proof. exact (TRANS (@lem4014568 A B _46357 f _46358 s _46356 t) (@lem4014660 A B f _46357 _46358 s _46356 t)). Qed.
Lemma lem4014662 {A B : Type'} (f : A -> B) (_46357 : A) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term485 A B t s f _46356 _46358 _46357) = (term522 A B f _46357 _46358 s _46356 t).
Proof. exact (TRANS (@lem4014361 A B t s f _46356 _46358 _46357) (@lem4014661 A B f _46357 _46358 s _46356 t)). Qed.
Lemma lem4014663 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4014664 {A B : Type'} (f : A -> B) (_46357 : A) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term523 A B t s f _46356 _46358 _46357) = (term524 A B f _46357 _46358 s _46356 t).
Proof. exact (MK_COMB (@lem4014663) (@lem4014662 A B f _46357 _46358 s _46356 t)). Qed.
Lemma lem4014680 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4014681 {A B : Type'} (t : B -> Prop) (_46357 : A) (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : (term525 A B t _46357 s f _46358 _46356) = (term526 A B t _46357 s f _46358 _46356).
Proof. exact (@lem4014680 (term155 A _46357 s) (term155 B _46356 t) (term527 A B _46357 s f _46358 _46356)). Qed.
Lemma lem4014695 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4014696 {A B : Type'} (_46357 : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : (term528 A B t _46357 s f _46358 _46356) = (term529 A B _46357 t s f _46358 _46356).
Proof. exact (@lem4014695 (term482 A B f _46357 _46356) (term155 B _46356 t) (term87 A B s f _46358 _46356)). Qed.
Lemma lem4014712 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4014713 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : (term530 A B t s f _46358 _46356) = (term531 A B s t f _46358 _46356).
Proof. exact (@lem4014712 (term155 A _46358 s) (term155 B _46356 t) (term482 A B f _46358 _46356)). Qed.
Lemma lem4014727 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4014728 {A B : Type'} (f : A -> B) (_46358 : A) (_46356 : B) (t : B -> Prop) : (term532 A B t f _46358 _46356) = (term506 A B f _46358 _46356 t).
Proof. exact (@lem4014727 (term482 A B f _46358 _46356) (term155 B _46356 t)). Qed.
Lemma lem4014736 {A : Type'} (_46358 : A) (s : A -> Prop) : (term112 A _46358 s) = (term112 A _46358 s).
Proof. exact (eq_refl (term112 A _46358 s)). Qed.
Lemma lem4014737 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) (t : B -> Prop) : (term531 A B s t f _46358 _46356) = (term507 A B s f _46358 _46356 t).
Proof. exact (MK_COMB (@lem4014736 A _46358 s) (@lem4014728 A B f _46358 _46356 t)). Qed.
Lemma lem4014741 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4014742 {A B : Type'} (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term507 A B s f _46358 _46356 t) = (term508 A B f _46358 s _46356 t).
Proof. exact (@lem4014741 (term482 A B f _46358 _46356) (term155 A _46358 s) (term155 B _46356 t)). Qed.
Lemma lem4014760 {A B : Type'} (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term531 A B s t f _46358 _46356) = (term508 A B f _46358 s _46356 t).
Proof. exact (TRANS (@lem4014737 A B s f _46358 _46356 t) (@lem4014742 A B f _46358 s _46356 t)). Qed.
Lemma lem4014761 {A B : Type'} (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term530 A B t s f _46358 _46356) = (term508 A B f _46358 s _46356 t).
Proof. exact (TRANS (@lem4014713 A B s t f _46358 _46356) (@lem4014760 A B f _46358 s _46356 t)). Qed.
Lemma lem4014762 {A B : Type'} (f : A -> B) (_46357 : A) (_46356 : B) : (term501 A B f _46357 _46356) = (term501 A B f _46357 _46356).
Proof. exact (eq_refl (term501 A B f _46357 _46356)). Qed.
Lemma lem4014763 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term529 A B _46357 t s f _46358 _46356) = (term515 A B _46357 f _46358 s _46356 t).
Proof. exact (MK_COMB (@lem4014762 A B f _46357 _46356) (@lem4014761 A B f _46358 s _46356 t)). Qed.
Lemma lem4014774 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term528 A B t _46357 s f _46358 _46356) = (term515 A B _46357 f _46358 s _46356 t).
Proof. exact (TRANS (@lem4014696 A B _46357 t s f _46358 _46356) (@lem4014763 A B _46357 f _46358 s _46356 t)). Qed.
Lemma lem4014775 {A : Type'} (_46357 : A) (s : A -> Prop) : (term112 A _46357 s) = (term112 A _46357 s).
Proof. exact (eq_refl (term112 A _46357 s)). Qed.
Lemma lem4014776 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term526 A B t _46357 s f _46358 _46356) = (term516 A B _46357 f _46358 s _46356 t).
Proof. exact (MK_COMB (@lem4014775 A _46357 s) (@lem4014774 A B _46357 f _46358 s _46356 t)). Qed.
Lemma lem4014780 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4014781 {A B : Type'} (_46357 : A) (f : A -> B) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term516 A B _46357 f _46358 s _46356 t) = (term517 A B _46357 f _46358 s _46356 t).
Proof. exact (@lem4014780 (term482 A B f _46357 _46356) (term155 A _46357 s) (term508 A B f _46358 s _46356 t)). Qed.
Lemma lem4014797 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4014798 {A B : Type'} (f : A -> B) (_46357 : A) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term518 A B _46357 f _46358 s _46356 t) = (term519 A B f _46357 _46358 s _46356 t).
Proof. exact (@lem4014797 (term482 A B f _46358 _46356) (term155 A _46357 s) (term520 A B _46358 s _46356 t)). Qed.
Lemma lem4014826 {A B : Type'} (f : A -> B) (_46357 : A) (_46356 : B) : (term501 A B f _46357 _46356) = (term501 A B f _46357 _46356).
Proof. exact (eq_refl (term501 A B f _46357 _46356)). Qed.
Lemma lem4014827 {A B : Type'} (f : A -> B) (_46357 : A) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term517 A B _46357 f _46358 s _46356 t) = (term521 A B f _46357 _46358 s _46356 t).
Proof. exact (MK_COMB (@lem4014826 A B f _46357 _46356) (@lem4014798 A B f _46357 _46358 s _46356 t)). Qed.
Lemma lem4014838 {A B : Type'} (f : A -> B) (_46357 : A) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term516 A B _46357 f _46358 s _46356 t) = (term521 A B f _46357 _46358 s _46356 t).
Proof. exact (TRANS (@lem4014781 A B _46357 f _46358 s _46356 t) (@lem4014827 A B f _46357 _46358 s _46356 t)). Qed.
Lemma lem4014839 {A B : Type'} (f : A -> B) (_46357 : A) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term526 A B t _46357 s f _46358 _46356) = (term521 A B f _46357 _46358 s _46356 t).
Proof. exact (TRANS (@lem4014776 A B _46357 f _46358 s _46356 t) (@lem4014838 A B f _46357 _46358 s _46356 t)). Qed.
Lemma lem4014840 {A B : Type'} (f : A -> B) (_46357 : A) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term525 A B t _46357 s f _46358 _46356) = (term521 A B f _46357 _46358 s _46356 t).
Proof. exact (TRANS (@lem4014681 A B t _46357 s f _46358 _46356) (@lem4014839 A B f _46357 _46358 s _46356 t)). Qed.
Lemma lem4014841 {A : Type'} (_46358 : A) (_46357 : A) : (term509 A _46358 _46357) = (term509 A _46358 _46357).
Proof. exact (eq_refl (term509 A _46358 _46357)). Qed.
Lemma lem4014842 {A B : Type'} (f : A -> B) (_46357 : A) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : (term533 A B t _46357 s f _46358 _46356) = (term522 A B f _46357 _46358 s _46356 t).
Proof. exact (MK_COMB (@lem4014841 A _46358 _46357) (@lem4014840 A B f _46357 _46358 s _46356 t)). Qed.
Lemma lem4014853 {A B : Type'} (f : A -> B) (_46357 : A) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : ((term485 A B t s f _46356 _46358 _46357) = (term533 A B t _46357 s f _46358 _46356)) = ((term522 A B f _46357 _46358 s _46356 t) = (term522 A B f _46357 _46358 s _46356 t)).
Proof. exact (MK_COMB (@lem4014664 A B f _46357 _46358 s _46356 t) (@lem4014842 A B f _46357 _46358 s _46356 t)). Qed.
Lemma lem4014855 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4014856 (x : Prop) : (x = x) = True.
Proof. exact (@lem4014855 Prop x). Qed.
Lemma lem4014857 {A B : Type'} (f : A -> B) (_46357 : A) (_46358 : A) (s : A -> Prop) (_46356 : B) (t : B -> Prop) : ((term522 A B f _46357 _46358 s _46356 t) = (term522 A B f _46357 _46358 s _46356 t)) = True.
Proof. exact (@lem4014856 (term522 A B f _46357 _46358 s _46356 t)). Qed.
Lemma lem4014858 {A B : Type'} (t : B -> Prop) (_46357 : A) (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : ((term485 A B t s f _46356 _46358 _46357) = (term533 A B t _46357 s f _46358 _46356)) = True.
Proof. exact (TRANS (@lem4014853 A B f _46357 _46358 s _46356 t) (@lem4014857 A B f _46357 _46358 s _46356 t)). Qed.
Lemma lem4014859 {A B : Type'} (t : B -> Prop) (_46357 : A) (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : True = ((term485 A B t s f _46356 _46358 _46357) = (term533 A B t _46357 s f _46358 _46356)).
Proof. exact (SYM (@lem4014858 A B t _46357 s f _46358 _46356)). Qed.
Lemma lem4014860 {A B : Type'} (t : B -> Prop) (_46357 : A) (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : (term485 A B t s f _46356 _46358 _46357) = (term533 A B t _46357 s f _46358 _46356).
Proof. exact (EQ_MP (@lem4014859 A B t _46357 s f _46358 _46356) (@lem0)). Qed.
Lemma lem4014861 {A B : Type'} (_46357 : A) (_46358 : A) (_46356 : B) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x' s f) : term533 A B t _46357 s f _46358 _46356.
Proof. exact (EQ_MP (@lem4014860 A B t _46357 s f _46358 _46356) (@lem4014130 A B _46356 _46358 _46357 t x' s f h1)). Qed.
Lemma lem4014863 (b : Prop) (a : Prop) : (a \/ b) = (term336 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4014864 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (_46356 : B) (_46358 : A) (_46357 : A) : (term533 A B t _46357 s f _46358 _46356) = (term534 A B t s f _46356 _46358 _46357).
Proof. exact (@lem4014863 (term525 A B t _46357 s f _46358 _46356) (_46358 = _46357)). Qed.
Lemma lem4014866 (a : Prop) (b : Prop) : (term355 a b) = (term356 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4014867 {A B : Type'} (t : B -> Prop) (_46357 : A) (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : (term535 A B t _46357 s f _46358 _46356) = (term536 A B t _46357 s f _46358 _46356).
Proof. exact (@lem4014866 (term155 B _46356 t) (term537 A B _46357 s f _46358 _46356)). Qed.
Lemma lem4014869 (a : Prop) : (term49 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4014870 {B : Type'} (_46356 : B) (t : B -> Prop) : (term338 B _46356 t) = (@IN B _46356 t).
Proof. exact (@lem4014869 (@IN B _46356 t)). Qed.
Lemma lem4014871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4014872 {B : Type'} (_46356 : B) (t : B -> Prop) : (term538 B _46356 t) = (term206 B _46356 t).
Proof. exact (MK_COMB (@lem4014871) (@lem4014870 B _46356 t)). Qed.
Lemma lem4014874 (a : Prop) (b : Prop) : (term355 a b) = (term356 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4014875 {A B : Type'} (_46357 : A) (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : (term539 A B _46357 s f _46358 _46356) = (term540 A B _46357 s f _46358 _46356).
Proof. exact (@lem4014874 (term155 A _46357 s) (term527 A B _46357 s f _46358 _46356)). Qed.
Lemma lem4014877 (a : Prop) : (term49 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4014878 {A : Type'} (_46357 : A) (s : A -> Prop) : (term338 A _46357 s) = (@IN A _46357 s).
Proof. exact (@lem4014877 (@IN A _46357 s)). Qed.
Lemma lem4014879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4014880 {A : Type'} (_46357 : A) (s : A -> Prop) : (term538 A _46357 s) = (term206 A _46357 s).
Proof. exact (MK_COMB (@lem4014879) (@lem4014878 A _46357 s)). Qed.
Lemma lem4014882 (a : Prop) (b : Prop) : (term355 a b) = (term356 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4014883 {A B : Type'} (_46357 : A) (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : (term541 A B _46357 s f _46358 _46356) = (term542 A B _46357 s f _46358 _46356).
Proof. exact (@lem4014882 (term482 A B f _46357 _46356) (term87 A B s f _46358 _46356)). Qed.
Lemma lem4014885 (a : Prop) : (term49 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4014886 {A B : Type'} (f : A -> B) (_46357 : A) (_46356 : B) : (term543 A B f _46357 _46356) = ((f _46357) = _46356).
Proof. exact (@lem4014885 ((f _46357) = _46356)). Qed.
Lemma lem4014887 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4014888 {A B : Type'} (f : A -> B) (_46357 : A) (_46356 : B) : (term544 A B f _46357 _46356) = (term545 A B f _46357 _46356).
Proof. exact (MK_COMB (@lem4014887) (@lem4014886 A B f _46357 _46356)). Qed.
Lemma lem4014890 (a : Prop) (b : Prop) : (term355 a b) = (term356 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4014891 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : (term546 A B s f _46358 _46356) = (term547 A B s f _46358 _46356).
Proof. exact (@lem4014890 (term155 A _46358 s) (term482 A B f _46358 _46356)). Qed.
Lemma lem4014893 (a : Prop) : (term49 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4014894 {A : Type'} (_46358 : A) (s : A -> Prop) : (term338 A _46358 s) = (@IN A _46358 s).
Proof. exact (@lem4014893 (@IN A _46358 s)). Qed.
Lemma lem4014895 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4014896 {A : Type'} (_46358 : A) (s : A -> Prop) : (term538 A _46358 s) = (term206 A _46358 s).
Proof. exact (MK_COMB (@lem4014895) (@lem4014894 A _46358 s)). Qed.
Lemma lem4014898 (a : Prop) : (term49 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4014899 {A B : Type'} (f : A -> B) (_46358 : A) (_46356 : B) : (term543 A B f _46358 _46356) = ((f _46358) = _46356).
Proof. exact (@lem4014898 ((f _46358) = _46356)). Qed.
Lemma lem4014900 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : (term547 A B s f _46358 _46356) = (term72 A B s f _46358 _46356).
Proof. exact (MK_COMB (@lem4014896 A _46358 s) (@lem4014899 A B f _46358 _46356)). Qed.
Lemma lem4014901 {A B : Type'} (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : (term546 A B s f _46358 _46356) = (term72 A B s f _46358 _46356).
Proof. exact (TRANS (@lem4014891 A B s f _46358 _46356) (@lem4014900 A B s f _46358 _46356)). Qed.
Lemma lem4014902 {A B : Type'} (_46357 : A) (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : (term542 A B _46357 s f _46358 _46356) = (term548 A B _46357 s f _46358 _46356).
Proof. exact (MK_COMB (@lem4014888 A B f _46357 _46356) (@lem4014901 A B s f _46358 _46356)). Qed.
Lemma lem4014903 {A B : Type'} (_46357 : A) (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : (term541 A B _46357 s f _46358 _46356) = (term548 A B _46357 s f _46358 _46356).
Proof. exact (TRANS (@lem4014883 A B _46357 s f _46358 _46356) (@lem4014902 A B _46357 s f _46358 _46356)). Qed.
Lemma lem4014904 {A B : Type'} (_46357 : A) (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : (term540 A B _46357 s f _46358 _46356) = (term549 A B _46357 s f _46358 _46356).
Proof. exact (MK_COMB (@lem4014880 A _46357 s) (@lem4014903 A B _46357 s f _46358 _46356)). Qed.
Lemma lem4014905 {A B : Type'} (_46357 : A) (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : (term539 A B _46357 s f _46358 _46356) = (term549 A B _46357 s f _46358 _46356).
Proof. exact (TRANS (@lem4014875 A B _46357 s f _46358 _46356) (@lem4014904 A B _46357 s f _46358 _46356)). Qed.
Lemma lem4014906 {A B : Type'} (t : B -> Prop) (_46357 : A) (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : (term536 A B t _46357 s f _46358 _46356) = (term550 A B t _46357 s f _46358 _46356).
Proof. exact (MK_COMB (@lem4014872 B _46356 t) (@lem4014905 A B _46357 s f _46358 _46356)). Qed.
Lemma lem4014907 {A B : Type'} (t : B -> Prop) (_46357 : A) (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : (term535 A B t _46357 s f _46358 _46356) = (term550 A B t _46357 s f _46358 _46356).
Proof. exact (TRANS (@lem4014867 A B t _46357 s f _46358 _46356) (@lem4014906 A B t _46357 s f _46358 _46356)). Qed.
Lemma lem4014908 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4014909 {A B : Type'} (t : B -> Prop) (_46357 : A) (s : A -> Prop) (f : A -> B) (_46358 : A) (_46356 : B) : (term551 A B t _46357 s f _46358 _46356) = (term552 A B t _46357 s f _46358 _46356).
Proof. exact (MK_COMB (@lem4014908) (@lem4014907 A B t _46357 s f _46358 _46356)). Qed.
Lemma lem4014910 {A : Type'} (_46358 : A) (_46357 : A) : (_46358 = _46357) = (_46358 = _46357).
Proof. exact (eq_refl (_46358 = _46357)). Qed.
Lemma lem4014911 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (_46356 : B) (_46358 : A) (_46357 : A) : (term534 A B t s f _46356 _46358 _46357) = (term553 A B t s f _46356 _46358 _46357).
Proof. exact (MK_COMB (@lem4014909 A B t _46357 s f _46358 _46356) (@lem4014910 A _46358 _46357)). Qed.
Lemma lem4014912 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (_46356 : B) (_46358 : A) (_46357 : A) : (term533 A B t _46357 s f _46358 _46356) = (term553 A B t s f _46356 _46358 _46357).
Proof. exact (TRANS (@lem4014864 A B t s f _46356 _46358 _46357) (@lem4014911 A B t s f _46356 _46358 _46357)). Qed.
Lemma lem4014914 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : term554 A B s x f y.
Proof. exact (conj (@lem4014347 A B s f x y h1) (@lem4014354 A B s f x y h1)). Qed.
Lemma lem4014915 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : term555 A B s x f y.
Proof. exact (conj (@lem4014340 A B f y) (@lem4014914 A B s f x y h1)). Qed.
Lemma lem4014916 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : term556 A B s x f y.
Proof. exact (conj (@lem4014331 A B s f x y h1) (@lem4014915 A B s f x y h1)). Qed.
Lemma lem4014917 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term30 A B s f t) (h2 : term423 A B s f x y) : term557 A B t s x f y.
Proof. exact (conj (@lem4014324 A B t s f x y h1 h2) (@lem4014916 A B s f x y h2)). Qed.
Lemma lem4014919 {A B : Type'} (_46356 : B) (_46358 : A) (_46357 : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x' s f) : term553 A B t s f _46356 _46358 _46357.
Proof. exact (EQ_MP (@lem4014912 A B t s f _46356 _46358 _46357) (@lem4014861 A B _46357 _46358 _46356 t x' s f h1)). Qed.
Lemma lem4014920 {A B : Type'} (_46356 : B) (_46358 : A) (_46357 : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x' s f) : term553 A B t s f _46356 _46358 _46357.
Proof. exact (@lem4014919 A B _46356 _46358 _46357 t x' s f h1). Qed.
Lemma lem4014921 {A B : Type'} (x : A) (y : A) (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term189 A B t x' s f) : term558 A B t s f x y.
Proof. exact (@lem4014920 A B (f y) x y t x' s f h1). Qed.
Lemma lem4014924 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term30 A B s f t) (h2 : term189 A B t x' s f) (h3 : term423 A B s f x y) : x = y.
Proof. exact (@lem4014921 A B x y t x' s f h2 (@lem4014917 A B t s f x y h1 h3)). Qed.
Lemma lem4014925 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term30 A B s f t) (h2 : term189 A B t x' s f) (h3 : term423 A B s f x y) : term559 A x y.
Proof. exact (fun h0 : term347 A x y => @lem4014924 A B t x' s f x y h1 h2 h3). Qed.
Lemma lem4014927 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4014928 {A : Type'} (x : A) (y : A) : (term559 A x y) = (x = y).
Proof. exact (@lem4014927 (x = y)). Qed.
Lemma lem4014929 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term30 A B s f t) (h2 : term189 A B t x' s f) (h3 : term423 A B s f x y) : x = y.
Proof. exact (EQ_MP (@lem4014928 A x y) (@lem4014925 A B t x' s f x y h1 h2 h3)). Qed.
Lemma lem4014932 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4014934 {A : Type'} (x : A) (y : A) : (term347 A x y) = (term560 A x y).
Proof. exact (@lem4014932 (x = y)). Qed.
Lemma lem4014937 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term423 A B s f x y) : term560 A x y.
Proof. exact (EQ_MP (@lem4014934 A x y) (@lem4014098 A B s f x y h1)). Qed.
Lemma lem4014940 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term30 A B s f t) (h2 : term189 A B t x' s f) (h3 : term423 A B s f x y) : False.
Proof. exact (@lem4014937 A B s f x y h3 (@lem4014929 A B t x' s f x y h1 h2 h3)). Qed.
Lemma lem4014941 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term30 A B s f t) (h2 : term189 A B t x' s f) (h3 : term423 A B s f x y) : term382.
Proof. exact (fun h0 : ~ False => @lem4014940 A B t x' s f x y h1 h2 h3). Qed.
Lemma lem4014943 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4014944 : term382 = False.
Proof. exact (@lem4014943 False). Qed.
Lemma lem4014945 {A B : Type'} (t : B -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) (h1 : term30 A B s f t) (h2 : term189 A B t x' s f) (h3 : term423 A B s f x y) : False.
Proof. exact (EQ_MP (@lem4014944) (@lem4014941 A B t x' s f x y h1 h2 h3)). Qed.
Lemma lem4015021 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4015022 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term561 A s.
Proof. exact (fun h0 : term441 A s => @lem4015021 A s h1). Qed.
Lemma lem4015024 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4015025 {A : Type'} (s : A -> Prop) : (term561 A s) = (@FINITE A s).
Proof. exact (@lem4015024 (@FINITE A s)). Qed.
Lemma lem4015026 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4015025 A s) (@lem4015022 A s h1)). Qed.
Lemma lem4015029 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4015031 {A : Type'} (s : A -> Prop) : (term441 A s) = (term562 A s).
Proof. exact (@lem4015029 (@FINITE A s)). Qed.
Lemma lem4015034 {A : Type'} (s : A -> Prop) (h1 : term441 A s) : term562 A s.
Proof. exact (EQ_MP (@lem4015031 A s) (@lem4014152 A s h1)). Qed.
Lemma lem4015037 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term441 A s) : False.
Proof. exact (@lem4015034 A s h2 (@lem4015026 A s h1)). Qed.
Lemma lem4015038 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term441 A s) : term382.
Proof. exact (fun h0 : ~ False => @lem4015037 A s h1 h2). Qed.
Lemma lem4015040 (p : Prop) : (term332 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4015041 : term382 = False.
Proof. exact (@lem4015040 False). Qed.
Lemma lem4015042 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term441 A s) : False.
Proof. exact (EQ_MP (@lem4015041) (@lem4015038 A s h1 h2)). Qed.
Lemma lem4015043 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term441 A s) : (term441 A s) = False.
Proof. exact (prop_ext (fun h3 : term441 A s => @lem4015042 A s h1 h2) (fun h3 : False => @lem4014152 A s h2)). Qed.
Lemma lem4015044 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term441 A s) : False.
Proof. exact (EQ_MP (@lem4015043 A s h1 h2) (@lem4014152 A s h2)). Qed.
Lemma lem4015045 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term441 A s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem4015044 A s h1 h2) (fun h3 : False => @lem4014144 A s h1)). Qed.
Lemma lem4015046 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term441 A s) : False.
Proof. exact (EQ_MP (@lem4015045 A s h1 h2) (@lem4014144 A s h1)). Qed.
Lemma lem4015047 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term441 A s) : (term441 A s) = False.
Proof. exact (prop_ext (fun h3 : term441 A s => @lem4015046 A s h1 h2) (fun h3 : False => @lem4014056 A s h2)). Qed.
Lemma lem4015048 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term441 A s) : False.
Proof. exact (EQ_MP (@lem4015047 A s h1 h2) (@lem4014056 A s h2)). Qed.
Lemma lem4015049 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term441 A s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem4015048 A s h1 h2) (fun h3 : False => @lem4013857 A s h1)). Qed.
Lemma lem4015050 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term441 A s) : False.
Proof. exact (EQ_MP (@lem4015049 A s h1 h2) (@lem4013857 A s h1)). Qed.
Lemma lem4015051 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term441 A s) : (term441 A s) = False.
Proof. exact (prop_ext (fun h3 : term441 A s => @lem4015050 A s h1 h2) (fun h3 : False => @lem4014056 A s h2)). Qed.
Lemma lem4015052 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term441 A s) : False.
Proof. exact (EQ_MP (@lem4015051 A s h1 h2) (@lem4014056 A s h2)). Qed.
Lemma lem4015053 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term441 A s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem4015052 A s h1 h2) (fun h3 : False => @lem4013857 A s h1)). Qed.
Lemma lem4015054 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term441 A s) : False.
Proof. exact (EQ_MP (@lem4015053 A s h1 h2) (@lem4013857 A s h1)). Qed.
Lemma lem4015055 {A B : Type'} (t : B -> Prop) (x' : B -> A) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term189 A B t x' s f) (h3 : @FINITE A s) (h4 : term474 A B f x y s) : False.
Proof. exact (or_elim (@lem4013539 A B f x y s h4) (fun h0 : term423 A B s f x y => @lem4014945 A B t x' s f x y h1 h2 h0) (fun h0 : term441 A s => @lem4015054 A s h3 h0)). Qed.
Lemma lem4015056 {A B : Type'} (t : B -> Prop) (x' : B -> A) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term189 A B t x' s f) (h3 : @FINITE A s) (h4 : term474 A B f x y s) : (term189 A B t x' s f) = False.
Proof. exact (prop_ext (fun h5 : term189 A B t x' s f => @lem4015055 A B t x' f x y s h1 h2 h3 h4) (fun h5 : False => @lem4013630 A B t x' s f h2)). Qed.
Lemma lem4015057 {A B : Type'} (t : B -> Prop) (x' : B -> A) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term189 A B t x' s f) (h3 : @FINITE A s) (h4 : term474 A B f x y s) : False.
Proof. exact (EQ_MP (@lem4015056 A B t x' f x y s h1 h2 h3 h4) (@lem4013630 A B t x' s f h2)). Qed.
Lemma lem4015058 {A B : Type'} (t : B -> Prop) (x' : B -> A) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term189 A B t x' s f) (h3 : @FINITE A s) (h4 : term474 A B f x y s) : (term474 A B f x y s) = False.
Proof. exact (prop_ext (fun h5 : term474 A B f x y s => @lem4015057 A B t x' f x y s h1 h2 h3 h4) (fun h5 : False => @lem4013539 A B f x y s h4)). Qed.
Lemma lem4015059 {A B : Type'} (t : B -> Prop) (x' : B -> A) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term189 A B t x' s f) (h3 : @FINITE A s) (h4 : term474 A B f x y s) : False.
Proof. exact (EQ_MP (@lem4015058 A B t x' f x y s h1 h2 h3 h4) (@lem4013539 A B f x y s h4)). Qed.
Lemma lem4015060 {A B : Type'} (t : B -> Prop) (x' : B -> A) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term189 A B t x' s f) (h3 : @FINITE A s) (h4 : term474 A B f x y s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem4015059 A B t x' f x y s h1 h2 h3 h4) (fun h5 : False => @lem4013474 A s h3)). Qed.
Lemma lem4015061 {A B : Type'} (t : B -> Prop) (x' : B -> A) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term189 A B t x' s f) (h3 : @FINITE A s) (h4 : term474 A B f x y s) : False.
Proof. exact (EQ_MP (@lem4015060 A B t x' f x y s h1 h2 h3 h4) (@lem4013474 A s h3)). Qed.
Lemma lem4015062 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) (y : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) (h4 : term474 A B f x y s) : False.
Proof. exact (ex_elim (@lem4013318 A B t s f h2) (fun x' : B -> A => fun h0 : term191 A B t s f x' => @lem4015061 A B t x' f x y s h1 h0 h3 h4)). Qed.
Lemma lem4015063 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : term477 A B f x s) (h4 : @FINITE A s) : False.
Proof. exact (ex_elim (@lem4013468 A B f x s h3) (fun y : A => fun h0 : term476 A B f x s y => @lem4015062 A B t f x y s h1 h2 h4 h0)). Qed.
Lemma lem4015064 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) (h4 : term393 A B f s) : False.
Proof. exact (ex_elim (@lem4013467 A B f s h4) (fun x : A => fun h0 : term478 A B f s x => @lem4015063 A B t f x s h1 h2 h0 h3)). Qed.
Lemma lem4015065 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) (h4 : term393 A B f s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem4015064 A B t f s h1 h2 h3 h4) (fun h5 : False => @lem4012843 A s h3)). Qed.
Lemma lem4015066 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) (h4 : term393 A B f s) : False.
Proof. exact (EQ_MP (@lem4015065 A B t f s h1 h2 h3 h4) (@lem4012843 A s h3)). Qed.
Lemma lem4015067 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) (h4 : term393 A B f s) : (term393 A B f s) = False.
Proof. exact (prop_ext (fun h5 : term393 A B f s => @lem4015066 A B t f s h1 h2 h3 h4) (fun h5 : False => @lem4012837 A B f s h4)). Qed.
Lemma lem4015068 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) (h4 : term393 A B f s) : False.
Proof. exact (EQ_MP (@lem4015067 A B t f s h1 h2 h3 h4) (@lem4012837 A B f s h4)). Qed.
Lemma lem4015069 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) : term392 A B f s.
Proof. exact (fun h0 : term393 A B f s => @lem4015068 A B t f s h1 h2 h3 h0). Qed.
Lemma lem4015070 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) : term12 A B f s.
Proof. exact (EQ_MP (@lem4012836 A B f s) (@lem4015069 A B t f s h1 h2 h3)). Qed.
Lemma lem4015071 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : @FINITE A s) : term400 A B t f s.
Proof. exact (fun h0 : term29 A B t s f => @lem4015070 A B t f s h1 h0 h2). Qed.
Lemma lem4015072 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term402 A B t f s.
Proof. exact (fun h0 : term30 A B s f t => @lem4015071 A B f t s h0 h1). Qed.
Lemma lem4015073 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term403 A B t f s.
Proof. exact (fun h0 : @FINITE A s => @lem4015072 A B t f s h0). Qed.
Lemma lem4015078 {A B : Type'} (f : A -> B) (s : A -> Prop) : term407 A B f s.
Proof. exact (fun t : B -> Prop => @lem4015073 A B t f s). Qed.
Lemma lem4015083 {A B : Type'} (s : A -> Prop) : term411 A B s.
Proof. exact (fun f : A -> B => @lem4015078 A B f s). Qed.
Lemma lem4015088 {A B : Type'} : term415 A B.
Proof. exact (fun s : A -> Prop => @lem4015083 A B s). Qed.
Lemma lem4015089 {A B : Type'} : term414 A B.
Proof. exact (EQ_MP (@lem4012829 A B) (@lem4015088 A B)). Qed.
Lemma lem4015090 {A B : Type'} (s : A -> Prop) : term563 A B s.
Proof. exact (@lem4015089 A B s). Qed.
Lemma lem4015091 {A B : Type'} (s : A -> Prop) : (term563 A B s) = (term410 A B s).
Proof. exact (eq_refl (term563 A B s)). Qed.
Lemma lem4015092 {A B : Type'} (s : A -> Prop) : term410 A B s.
Proof. exact (EQ_MP (@lem4015091 A B s) (@lem4015090 A B s)). Qed.
Lemma lem4015093 {A B : Type'} (s : A -> Prop) (f : A -> B) : term564 A B s f.
Proof. exact (@lem4015092 A B s f). Qed.
Lemma lem4015094 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term564 A B s f) = (term406 A B f s).
Proof. exact (eq_refl (term564 A B s f)). Qed.
Lemma lem4015095 {A B : Type'} (f : A -> B) (s : A -> Prop) : term406 A B f s.
Proof. exact (EQ_MP (@lem4015094 A B f s) (@lem4015093 A B s f)). Qed.
Lemma lem4015096 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : term565 A B f s t.
Proof. exact (@lem4015095 A B f s t). Qed.
Lemma lem4015097 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term565 A B f s t) = (term394 A B t f s).
Proof. exact (eq_refl (term565 A B f s t)). Qed.
Lemma lem4015098 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term394 A B t f s.
Proof. exact (EQ_MP (@lem4015097 A B t f s) (@lem4015096 A B f s t)). Qed.
Lemma lem4015100 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term394 A B t f s.
Proof. exact (@lem4012606 A B t f s (@lem4015098 A B t f s)). Qed.
Lemma lem4015101 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term401 A B t f s.
Proof. exact (@lem4015100 A B t f s (@lem4010162 A s h1)). Qed.
Lemma lem4015102 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : @FINITE A s) : term399 A B t f s.
Proof. exact (@lem4015101 A B t f s h2 (@lem4010164 A B s f t h1)). Qed.
Lemma lem4015103 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) : term392 A B f s.
Proof. exact (@lem4015102 A B f t s h1 h3 (@lem4010163 A B t s f h2)). Qed.
Lemma lem4015104 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) (h4 : term393 A B f s) : False.
Proof. exact (@lem4015103 A B t f s h1 h2 h3 (@lem4012590 A B f s h4)). Qed.
Lemma lem4015105 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) (h4 : term393 A B f s) : (term393 A B f s) = False.
Proof. exact (prop_ext (fun h5 : term393 A B f s => @lem4015104 A B t f s h1 h2 h3 h4) (fun h5 : False => @lem4012590 A B f s h4)). Qed.
Lemma lem4015106 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) (h4 : term393 A B f s) : False.
Proof. exact (EQ_MP (@lem4015105 A B t f s h1 h2 h3 h4) (@lem4012590 A B f s h4)). Qed.
Lemma lem4015107 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) : term392 A B f s.
Proof. exact (fun h0 : term393 A B f s => @lem4015106 A B t f s h1 h2 h3 h0). Qed.
Lemma lem4015108 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) : term12 A B f s.
Proof. exact (EQ_MP (@lem4012589 A B f s) (@lem4015107 A B t f s h1 h2 h3)). Qed.
Lemma lem4015109 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) : (term13 A B f s) = (@CARD A s).
Proof. exact (@lem4012585 A B f s (@lem4015108 A B t f s h1 h2 h3)). Qed.
Lemma lem4015110 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) (h4 : t = (@IMAGE A B f s)) : (@CARD B t) = (@CARD A s).
Proof. exact (EQ_MP (@lem4010178 A B t f s h4) (@lem4015109 A B t f s h1 h2 h3)). Qed.
Lemma lem4015111 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) : (t = (@IMAGE A B f s)) = ((@CARD B t) = (@CARD A s)).
Proof. exact (prop_ext (fun h4 : t = (@IMAGE A B f s) => @lem4015110 A B t f s h1 h2 h3 h4) (fun h4 : (@CARD B t) = (@CARD A s) => @lem4012582 A B t f s h1 h2 h3)). Qed.
Lemma lem4015112 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) : (@CARD B t) = (@CARD A s).
Proof. exact (EQ_MP (@lem4015111 A B t f s h1 h2 h3) (@lem4012582 A B t f s h1 h2 h3)). Qed.
Lemma lem4015113 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term27 A B t s f) : term28 A B t s f.
Proof. exact (proj2 (@lem4010160 A B t s f h1)). Qed.
Lemma lem4015114 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term27 A B t s f) : @FINITE A s.
Proof. exact (proj1 (@lem4010160 A B t s f h1)). Qed.
Lemma lem4015115 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term28 A B t s f) : term29 A B t s f.
Proof. exact (proj2 (@lem4010161 A B t s f h1)). Qed.
Lemma lem4015116 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term28 A B t s f) : term30 A B s f t.
Proof. exact (proj1 (@lem4010161 A B t s f h1)). Qed.
Lemma lem4015117 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) : (term29 A B t s f) = ((@CARD B t) = (@CARD A s)).
Proof. exact (prop_ext (fun h4 : term29 A B t s f => @lem4015112 A B t f s h1 h2 h3) (fun h4 : (@CARD B t) = (@CARD A s) => @lem4010163 A B t s f h2)). Qed.
Lemma lem4015118 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) : (@CARD B t) = (@CARD A s).
Proof. exact (EQ_MP (@lem4015117 A B t f s h1 h2 h3) (@lem4010163 A B t s f h2)). Qed.
Lemma lem4015119 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) : (term30 A B s f t) = ((@CARD B t) = (@CARD A s)).
Proof. exact (prop_ext (fun h4 : term30 A B s f t => @lem4015118 A B t f s h1 h2 h3) (fun h4 : (@CARD B t) = (@CARD A s) => @lem4010164 A B s f t h1)). Qed.
Lemma lem4015120 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term30 A B s f t) (h2 : term29 A B t s f) (h3 : @FINITE A s) : (@CARD B t) = (@CARD A s).
Proof. exact (EQ_MP (@lem4015119 A B t f s h1 h2 h3) (@lem4010164 A B s f t h1)). Qed.
Lemma lem4015121 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term30 A B s f t) (h2 : @FINITE A s) (h3 : term28 A B t s f) : (term29 A B t s f) = ((@CARD B t) = (@CARD A s)).
Proof. exact (prop_ext (fun h4 : term29 A B t s f => @lem4015120 A B t f s h1 h4 h2) (fun h4 : (@CARD B t) = (@CARD A s) => @lem4015115 A B t s f h3)). Qed.
Lemma lem4015122 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term30 A B s f t) (h2 : @FINITE A s) (h3 : term28 A B t s f) : (@CARD B t) = (@CARD A s).
Proof. exact (EQ_MP (@lem4015121 A B t s f h1 h2 h3) (@lem4015115 A B t s f h3)). Qed.
Lemma lem4015123 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : @FINITE A s) (h2 : term28 A B t s f) : (term30 A B s f t) = ((@CARD B t) = (@CARD A s)).
Proof. exact (prop_ext (fun h3 : term30 A B s f t => @lem4015122 A B t s f h3 h1 h2) (fun h3 : (@CARD B t) = (@CARD A s) => @lem4015116 A B t s f h2)). Qed.
Lemma lem4015124 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : @FINITE A s) (h2 : term28 A B t s f) : (@CARD B t) = (@CARD A s).
Proof. exact (EQ_MP (@lem4015123 A B t s f h1 h2) (@lem4015116 A B t s f h2)). Qed.
Lemma lem4015125 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : @FINITE A s) (h2 : term28 A B t s f) : (@FINITE A s) = ((@CARD B t) = (@CARD A s)).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem4015124 A B t s f h1 h2) (fun h3 : (@CARD B t) = (@CARD A s) => @lem4010162 A s h1)). Qed.
Lemma lem4015126 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : @FINITE A s) (h2 : term28 A B t s f) : (@CARD B t) = (@CARD A s).
Proof. exact (EQ_MP (@lem4015125 A B t s f h1 h2) (@lem4010162 A s h1)). Qed.
Lemma lem4015127 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : @FINITE A s) (h2 : term27 A B t s f) : (term28 A B t s f) = ((@CARD B t) = (@CARD A s)).
Proof. exact (prop_ext (fun h3 : term28 A B t s f => @lem4015126 A B t s f h1 h3) (fun h3 : (@CARD B t) = (@CARD A s) => @lem4015113 A B t s f h2)). Qed.
Lemma lem4015128 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : @FINITE A s) (h2 : term27 A B t s f) : (@CARD B t) = (@CARD A s).
Proof. exact (EQ_MP (@lem4015127 A B t s f h1 h2) (@lem4015113 A B t s f h2)). Qed.
Lemma lem4015129 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term27 A B t s f) : (@FINITE A s) = ((@CARD B t) = (@CARD A s)).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem4015128 A B t s f h2 h1) (fun h2 : (@CARD B t) = (@CARD A s) => @lem4015114 A B t s f h1)). Qed.
Lemma lem4015130 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term27 A B t s f) : (@CARD B t) = (@CARD A s).
Proof. exact (EQ_MP (@lem4015129 A B t s f h1) (@lem4015114 A B t s f h1)). Qed.
Lemma lem4015131 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : term566 A B f t s.
Proof. exact (fun h0 : term27 A B t s f => @lem4015130 A B t s f h0). Qed.
Lemma lem4015136 {A B : Type'} (f : A -> B) (s : A -> Prop) : term567 A B f s.
Proof. exact (fun t : B -> Prop => @lem4015131 A B f t s). Qed.
Lemma lem4015141 {A B : Type'} (f : A -> B) : term568 A B f.
Proof. exact (fun s : A -> Prop => @lem4015136 A B f s). Qed.
Lemma lem4015146 {A B : Type'} : term569 A B.
Proof. exact (fun f : A -> B => @lem4015141 A B f). Qed.
