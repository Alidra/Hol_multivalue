Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_UNION_RZERO_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import IN_DIFF_spec.
Require Import IN_UNION_spec.
Require Import NSUM_SUPERSET_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
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
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Lemma lem6963087 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem6963088 {_127719 : Type'} (s : _127719 -> Prop) (t : _127719 -> Prop) : (s = t) = (term0 _127719 s t).
Proof. exact (@lem6963087 _127719 s t). Qed.
Lemma lem6963089 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : ((@UNION _127719 u v) = (term1 _127719 v u)) = (term2 _127719 v u).
Proof. exact (@lem6963088 _127719 (@UNION _127719 u v) (term1 _127719 v u)). Qed.
Lemma lem6963098 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : (term2 _127719 v u) = ((@UNION _127719 u v) = (term1 _127719 v u)).
Proof. exact (SYM (@lem6963089 _127719 v u)). Qed.
Lemma lem6963106 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term3 A x s t) = (term4 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem6963107 {_127719 : Type'} (s : _127719 -> Prop) (x : _127719) (t : _127719 -> Prop) : (term3 _127719 x s t) = (term4 _127719 s x t).
Proof. exact (@lem6963106 _127719 s x t). Qed.
Lemma lem6963108 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (v : _127719 -> Prop) : (term3 _127719 x u v) = (term4 _127719 u x v).
Proof. exact (@lem6963107 _127719 u x v). Qed.
Lemma lem6963112 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6963113 {_127719 : Type'} (P : _127719 -> Prop) (x : _127719) : (@IN _127719 x P) = (P x).
Proof. exact (@lem6963112 _127719 P x). Qed.
Lemma lem6963114 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) : (@IN _127719 x u) = (u x).
Proof. exact (@lem6963113 _127719 u x). Qed.
Lemma lem6963115 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6963116 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) : (term5 _127719 x u) = (term6 _127719 u x).
Proof. exact (MK_COMB (@lem6963115) (@lem6963114 _127719 u x)). Qed.
Lemma lem6963118 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6963119 {_127719 : Type'} (P : _127719 -> Prop) (x : _127719) : (@IN _127719 x P) = (P x).
Proof. exact (@lem6963118 _127719 P x). Qed.
Lemma lem6963120 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) : (@IN _127719 x v) = (v x).
Proof. exact (@lem6963119 _127719 v x). Qed.
Lemma lem6963121 {_127719 : Type'} (u : _127719 -> Prop) (v : _127719 -> Prop) (x : _127719) : (term4 _127719 u x v) = (term7 _127719 u v x).
Proof. exact (MK_COMB (@lem6963116 _127719 u x) (@lem6963120 _127719 v x)). Qed.
Lemma lem6963124 {_127719 : Type'} (u : _127719 -> Prop) (v : _127719 -> Prop) (x : _127719) : (term3 _127719 x u v) = (term7 _127719 u v x).
Proof. exact (TRANS (@lem6963108 _127719 u x v) (@lem6963121 _127719 u v x)). Qed.
Lemma lem6963125 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6963126 {_127719 : Type'} (u : _127719 -> Prop) (v : _127719 -> Prop) (x : _127719) : (term8 _127719 x u v) = (term9 _127719 u v x).
Proof. exact (MK_COMB (@lem6963125) (@lem6963124 _127719 u v x)). Qed.
Lemma lem6963128 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term3 A x s t) = (term4 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem6963129 {_127719 : Type'} (s : _127719 -> Prop) (x : _127719) (t : _127719 -> Prop) : (term3 _127719 x s t) = (term4 _127719 s x t).
Proof. exact (@lem6963128 _127719 s x t). Qed.
Lemma lem6963130 {_127719 : Type'} (x : _127719) (v : _127719 -> Prop) (u : _127719 -> Prop) : (term10 _127719 x v u) = (term11 _127719 x v u).
Proof. exact (@lem6963129 _127719 u x (@DIFF _127719 v u)). Qed.
Lemma lem6963134 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6963135 {_127719 : Type'} (P : _127719 -> Prop) (x : _127719) : (@IN _127719 x P) = (P x).
Proof. exact (@lem6963134 _127719 P x). Qed.
Lemma lem6963136 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) : (@IN _127719 x u) = (u x).
Proof. exact (@lem6963135 _127719 u x). Qed.
Lemma lem6963137 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6963138 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) : (term5 _127719 x u) = (term6 _127719 u x).
Proof. exact (MK_COMB (@lem6963137) (@lem6963136 _127719 u x)). Qed.
Lemma lem6963140 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A x s t) = (term13 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem6963141 {_127719 : Type'} (s : _127719 -> Prop) (x : _127719) (t : _127719 -> Prop) : (term12 _127719 x s t) = (term13 _127719 s x t).
Proof. exact (@lem6963140 _127719 s x t). Qed.
Lemma lem6963142 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (u : _127719 -> Prop) : (term12 _127719 x v u) = (term13 _127719 v x u).
Proof. exact (@lem6963141 _127719 v x u). Qed.
Lemma lem6963146 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6963147 {_127719 : Type'} (P : _127719 -> Prop) (x : _127719) : (@IN _127719 x P) = (P x).
Proof. exact (@lem6963146 _127719 P x). Qed.
Lemma lem6963148 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) : (@IN _127719 x v) = (v x).
Proof. exact (@lem6963147 _127719 v x). Qed.
Lemma lem6963149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6963150 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) : (term14 _127719 x v) = (term15 _127719 v x).
Proof. exact (MK_COMB (@lem6963149) (@lem6963148 _127719 v x)). Qed.
Lemma lem6963152 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6963153 {_127719 : Type'} (P : _127719 -> Prop) (x : _127719) : (@IN _127719 x P) = (P x).
Proof. exact (@lem6963152 _127719 P x). Qed.
Lemma lem6963154 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) : (@IN _127719 x u) = (u x).
Proof. exact (@lem6963153 _127719 u x). Qed.
Lemma lem6963155 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6963156 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) : (term16 _127719 x u) = (term17 _127719 u x).
Proof. exact (MK_COMB (@lem6963155) (@lem6963154 _127719 u x)). Qed.
Lemma lem6963157 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term13 _127719 v x u) = (term18 _127719 v u x).
Proof. exact (MK_COMB (@lem6963150 _127719 v x) (@lem6963156 _127719 u x)). Qed.
Lemma lem6963160 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term12 _127719 x v u) = (term18 _127719 v u x).
Proof. exact (TRANS (@lem6963142 _127719 v x u) (@lem6963157 _127719 v u x)). Qed.
Lemma lem6963161 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term11 _127719 x v u) = (term19 _127719 v u x).
Proof. exact (MK_COMB (@lem6963138 _127719 u x) (@lem6963160 _127719 v u x)). Qed.
Lemma lem6963164 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term10 _127719 x v u) = (term19 _127719 v u x).
Proof. exact (TRANS (@lem6963130 _127719 x v u) (@lem6963161 _127719 v u x)). Qed.
Lemma lem6963165 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : ((term3 _127719 x u v) = (term10 _127719 x v u)) = ((term7 _127719 u v x) = (term19 _127719 v u x)).
Proof. exact (MK_COMB (@lem6963126 _127719 u v x) (@lem6963164 _127719 v u x)). Qed.
Lemma lem6963168 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : (term20 _127719 v u) = (term21 _127719 v u).
Proof. exact (fun_ext (fun x : _127719 => @lem6963165 _127719 v u x)). Qed.
Lemma lem6963169 {_127719 : Type'} : (@all _127719) = (@all _127719).
Proof. exact (eq_refl (@all _127719)). Qed.
Lemma lem6963170 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : (term2 _127719 v u) = (term22 _127719 v u).
Proof. exact (MK_COMB (@lem6963169 _127719) (@lem6963168 _127719 v u)). Qed.
Lemma lem6963175 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : (term22 _127719 v u) = (term2 _127719 v u).
Proof. exact (SYM (@lem6963170 _127719 v u)). Qed.
Lemma lem6963177 (p : Prop) : p = (term23 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6963178 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : (term22 _127719 v u) = (term24 _127719 v u).
Proof. exact (@lem6963177 (term22 _127719 v u)). Qed.
Lemma lem6963179 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : (term24 _127719 v u) = (term22 _127719 v u).
Proof. exact (SYM (@lem6963178 _127719 v u)). Qed.
Lemma lem6963180 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (h1 : term25 _127719 v u) : term25 _127719 v u.
Proof. exact (h1). Qed.
Lemma lem6963183 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (h1 : term24 _127719 v u) : term24 _127719 v u.
Proof. exact (h1). Qed.
Lemma lem6963184 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : term26 _127719 v u.
Proof. exact (fun h0 : term24 _127719 v u => @lem6963183 _127719 v u h0). Qed.
Lemma lem6963185 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (h1 : term26 _127719 v u) : term26 _127719 v u.
Proof. exact (h1). Qed.
Lemma lem6963186 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (h1 : term24 _127719 v u) : term24 _127719 v u.
Proof. exact (h1). Qed.
Lemma lem6963187 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (h1 : term24 _127719 v u) (h2 : term26 _127719 v u) : term24 _127719 v u.
Proof. exact (@lem6963185 _127719 v u h2 (@lem6963186 _127719 v u h1)). Qed.
Lemma lem6963188 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (h1 : term24 _127719 v u) : term27 _127719 v u.
Proof. exact (fun h0 : term26 _127719 v u => @lem6963187 _127719 v u h1 h0). Qed.
Lemma lem6963189 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (h1 : term26 _127719 v u) : term26 _127719 v u.
Proof. exact (h1). Qed.
Lemma lem6963190 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (h1 : term24 _127719 v u) (h2 : term26 _127719 v u) : term24 _127719 v u.
Proof. exact (@lem6963188 _127719 v u h1 (@lem6963189 _127719 v u h2)). Qed.
Lemma lem6963191 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (h1 : term26 _127719 v u) : term26 _127719 v u.
Proof. exact (fun h0 : term24 _127719 v u => @lem6963190 _127719 v u h0 h1). Qed.
Lemma lem6963192 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : term28 _127719 v u.
Proof. exact (fun h0 : term26 _127719 v u => @lem6963191 _127719 v u h0). Qed.
Lemma lem6963195 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : term26 _127719 v u.
Proof. exact (@lem6963192 _127719 v u (@lem6963184 _127719 v u)). Qed.
Lemma lem6963196 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : term26 _127719 v u.
Proof. exact (@lem6963195 _127719 v u). Qed.
Lemma lem6963206 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6963207 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : (term24 _127719 v u) = (term29 _127719 v u).
Proof. exact (@lem6963206 (term25 _127719 v u)). Qed.
Lemma lem6963209 (t : Prop) : (term30 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6963210 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : (term29 _127719 v u) = (term22 _127719 v u).
Proof. exact (@lem6963209 (term22 _127719 v u)). Qed.
Lemma lem6963215 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : (term24 _127719 v u) = (term22 _127719 v u).
Proof. exact (TRANS (@lem6963207 _127719 v u) (@lem6963210 _127719 v u)). Qed.
Lemma lem6963222 {_127719 : Type'} (u : _127719 -> Prop) : (term31 _127719 u) = (term32 _127719 u).
Proof. exact (fun_ext (fun v : _127719 -> Prop => @lem6963215 _127719 v u)). Qed.
Lemma lem6963223 {_127719 : Type'} : (@all (_127719 -> Prop)) = (@all (_127719 -> Prop)).
Proof. exact (eq_refl (@all (_127719 -> Prop))). Qed.
Lemma lem6963224 {_127719 : Type'} (u : _127719 -> Prop) : (term33 _127719 u) = (term34 _127719 u).
Proof. exact (MK_COMB (@lem6963223 _127719) (@lem6963222 _127719 u)). Qed.
Lemma lem6963229 {_127719 : Type'} : (term35 _127719) = (term36 _127719).
Proof. exact (fun_ext (fun u : _127719 -> Prop => @lem6963224 _127719 u)). Qed.
Lemma lem6963230 {_127719 : Type'} : (@all (_127719 -> Prop)) = (@all (_127719 -> Prop)).
Proof. exact (eq_refl (@all (_127719 -> Prop))). Qed.
Lemma lem6963239 {_127719 : Type'} : (term37 _127719) = (term38 _127719).
Proof. exact (MK_COMB (@lem6963230 _127719) (@lem6963229 _127719)). Qed.
Lemma lem6963258 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : ((term7 _127719 u v x) = (term19 _127719 v u x)) = ((term7 _127719 u v x) = (term19 _127719 v u x)).
Proof. exact (eq_refl ((term7 _127719 u v x) = (term19 _127719 v u x))). Qed.
Lemma lem6963259 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : (term21 _127719 v u) = (term21 _127719 v u).
Proof. exact (fun_ext (fun x : _127719 => @lem6963258 _127719 v u x)). Qed.
Lemma lem6963260 {_127719 : Type'} : (@all _127719) = (@all _127719).
Proof. exact (eq_refl (@all _127719)). Qed.
Lemma lem6963261 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : (term22 _127719 v u) = (term22 _127719 v u).
Proof. exact (MK_COMB (@lem6963260 _127719) (@lem6963259 _127719 v u)). Qed.
Lemma lem6963262 {_127719 : Type'} (u : _127719 -> Prop) : (term32 _127719 u) = (term32 _127719 u).
Proof. exact (fun_ext (fun v : _127719 -> Prop => @lem6963261 _127719 v u)). Qed.
Lemma lem6963263 {_127719 : Type'} : (@all (_127719 -> Prop)) = (@all (_127719 -> Prop)).
Proof. exact (eq_refl (@all (_127719 -> Prop))). Qed.
Lemma lem6963264 {_127719 : Type'} (u : _127719 -> Prop) : (term34 _127719 u) = (term34 _127719 u).
Proof. exact (MK_COMB (@lem6963263 _127719) (@lem6963262 _127719 u)). Qed.
Lemma lem6963265 {_127719 : Type'} : (term36 _127719) = (term36 _127719).
Proof. exact (fun_ext (fun u : _127719 -> Prop => @lem6963264 _127719 u)). Qed.
Lemma lem6963266 {_127719 : Type'} : (@all (_127719 -> Prop)) = (@all (_127719 -> Prop)).
Proof. exact (eq_refl (@all (_127719 -> Prop))). Qed.
Lemma lem6963267 {_127719 : Type'} : (term38 _127719) = (term38 _127719).
Proof. exact (MK_COMB (@lem6963266 _127719) (@lem6963265 _127719)). Qed.
Lemma lem6963294 {_127719 : Type'} : (term37 _127719) = (term38 _127719).
Proof. exact (TRANS (@lem6963239 _127719) (@lem6963267 _127719)). Qed.
Lemma lem6963295 {_127719 : Type'} : (term38 _127719) = (term37 _127719).
Proof. exact (SYM (@lem6963294 _127719)). Qed.
Lemma lem6963297 (p : Prop) : p = (term23 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6963298 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : ((term7 _127719 u v x) = (term19 _127719 v u x)) = (term39 _127719 v u x).
Proof. exact (@lem6963297 ((term7 _127719 u v x) = (term19 _127719 v u x))). Qed.
Lemma lem6963299 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term39 _127719 v u x) = ((term7 _127719 u v x) = (term19 _127719 v u x)).
Proof. exact (SYM (@lem6963298 _127719 v u x)). Qed.
Lemma lem6963300 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term40 _127719 v u x) : term40 _127719 v u x.
Proof. exact (h1). Qed.
Lemma lem6963309 {_127719 : Type'} (u : _127719 -> Prop) (v : _127719 -> Prop) (x : _127719) : (term41 _127719 u v x) = (term42 _127719 u v x).
Proof. exact (@lem17160 (u x) (v x)). Qed.
Lemma lem6963320 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) : (term43 _127719 u x) = (u x).
Proof. exact (@lem16933 (u x)). Qed.
Lemma lem6963322 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) : (term44 _127719 v x) = (term44 _127719 v x).
Proof. exact (eq_refl (term44 _127719 v x)). Qed.
Lemma lem6963323 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term45 _127719 v u x) = (term46 _127719 v u x).
Proof. exact (MK_COMB (@lem6963322 _127719 v x) (@lem6963320 _127719 u x)). Qed.
Lemma lem6963324 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term47 _127719 v u x) = (term45 _127719 v u x).
Proof. exact (@lem17045 (v x) (term17 _127719 u x)). Qed.
Lemma lem6963325 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term47 _127719 v u x) = (term46 _127719 v u x).
Proof. exact (TRANS (@lem6963324 _127719 v u x) (@lem6963323 _127719 v u x)). Qed.
Lemma lem6963330 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) : (term48 _127719 u x) = (term48 _127719 u x).
Proof. exact (eq_refl (term48 _127719 u x)). Qed.
Lemma lem6963331 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term49 _127719 v u x) = (term50 _127719 v u x).
Proof. exact (MK_COMB (@lem6963330 _127719 u x) (@lem6963325 _127719 v u x)). Qed.
Lemma lem6963332 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term51 _127719 v u x) = (term49 _127719 v u x).
Proof. exact (@lem17160 (u x) (term18 _127719 v u x)). Qed.
Lemma lem6963333 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term51 _127719 v u x) = (term50 _127719 v u x).
Proof. exact (TRANS (@lem6963332 _127719 v u x) (@lem6963331 _127719 v u x)). Qed.
Lemma lem6963336 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term19 _127719 v u x) = (term19 _127719 v u x).
Proof. exact (eq_refl (term19 _127719 v u x)). Qed.
Lemma lem6963337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6963338 {_127719 : Type'} (u : _127719 -> Prop) (v : _127719 -> Prop) (x : _127719) : (term52 _127719 u v x) = (term53 _127719 u v x).
Proof. exact (MK_COMB (@lem6963337) (@lem6963309 _127719 u v x)). Qed.
Lemma lem6963339 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term54 _127719 v u x) = (term55 _127719 v u x).
Proof. exact (MK_COMB (@lem6963338 _127719 u v x) (@lem6963336 _127719 v u x)). Qed.
Lemma lem6963341 {_127719 : Type'} (u : _127719 -> Prop) (v : _127719 -> Prop) (x : _127719) : (term56 _127719 u v x) = (term56 _127719 u v x).
Proof. exact (eq_refl (term56 _127719 u v x)). Qed.
Lemma lem6963342 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term57 _127719 v u x) = (term58 _127719 v u x).
Proof. exact (MK_COMB (@lem6963341 _127719 u v x) (@lem6963333 _127719 v u x)). Qed.
Lemma lem6963343 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6963344 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term59 _127719 v u x) = (term60 _127719 v u x).
Proof. exact (MK_COMB (@lem6963343) (@lem6963342 _127719 v u x)). Qed.
Lemma lem6963345 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term61 _127719 v u x) = (term62 _127719 v u x).
Proof. exact (MK_COMB (@lem6963344 _127719 v u x) (@lem6963339 _127719 v u x)). Qed.
Lemma lem6963346 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term40 _127719 v u x) = (term61 _127719 v u x).
Proof. exact (@lem17646 (term7 _127719 u v x) (term19 _127719 v u x)). Qed.
Lemma lem6963351 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term40 _127719 v u x) = (term62 _127719 v u x).
Proof. exact (TRANS (@lem6963346 _127719 v u x) (@lem6963345 _127719 v u x)). Qed.
Lemma lem6963420 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term40 _127719 v u x) : term62 _127719 v u x.
Proof. exact (EQ_MP (@lem6963351 _127719 v u x) (@lem6963300 _127719 v u x h1)). Qed.
Lemma lem6963421 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term58 _127719 v u x) : term58 _127719 v u x.
Proof. exact (h1). Qed.
Lemma lem6963422 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term55 _127719 v u x) : term55 _127719 v u x.
Proof. exact (h1). Qed.
Lemma lem6963423 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term58 _127719 v u x) : term50 _127719 v u x.
Proof. exact (proj2 (@lem6963421 _127719 v u x h1)). Qed.
Lemma lem6963424 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term58 _127719 v u x) : term7 _127719 u v x.
Proof. exact (proj1 (@lem6963421 _127719 v u x h1)). Qed.
Lemma lem6963425 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term58 _127719 v u x) : term46 _127719 v u x.
Proof. exact (proj2 (@lem6963423 _127719 v u x h1)). Qed.
Lemma lem6963433 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term55 _127719 v u x) : term19 _127719 v u x.
Proof. exact (proj2 (@lem6963422 _127719 v u x h1)). Qed.
Lemma lem6963434 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term55 _127719 v u x) : term42 _127719 u v x.
Proof. exact (proj1 (@lem6963422 _127719 v u x h1)). Qed.
Lemma lem6963438 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term18 _127719 v u x) : term18 _127719 v u x.
Proof. exact (h1). Qed.
Lemma lem6963452 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem6963460 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) : term17 _127719 v x.
Proof. exact (h1). Qed.
Lemma lem6963464 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : v x) : v x.
Proof. exact (h1). Qed.
Lemma lem6963472 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem6963476 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem6963484 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem6963500 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem6963518 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term58 _127719 v u x) : term17 _127719 u x.
Proof. exact (proj1 (@lem6963423 _127719 v u x h1)). Qed.
Lemma lem6963522 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem6963526 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) : term17 _127719 v x.
Proof. exact (h1). Qed.
Lemma lem6963528 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : v x) : v x.
Proof. exact (h1). Qed.
Lemma lem6963530 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term58 _127719 v u x) : term17 _127719 u x.
Proof. exact (proj1 (@lem6963423 _127719 v u x h1)). Qed.
Lemma lem6963532 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem6963534 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem6963536 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term58 _127719 v u x) : term17 _127719 u x.
Proof. exact (proj1 (@lem6963423 _127719 v u x h1)). Qed.
Lemma lem6963538 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem6963542 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term55 _127719 v u x) : term17 _127719 u x.
Proof. exact (proj1 (@lem6963434 _127719 v u x h1)). Qed.
Lemma lem6963546 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem6963550 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term55 _127719 v u x) : term17 _127719 v x.
Proof. exact (proj2 (@lem6963434 _127719 v u x h1)). Qed.
Lemma lem6963556 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem6963557 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : term63 _127719 u x.
Proof. exact (fun h0 : term17 _127719 u x => @lem6963556 _127719 u x h1). Qed.
Lemma lem6963559 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6963560 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) : (term63 _127719 u x) = (u x).
Proof. exact (@lem6963559 (u x)). Qed.
Lemma lem6963561 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (EQ_MP (@lem6963560 _127719 u x) (@lem6963557 _127719 u x h1)). Qed.
Lemma lem6963564 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6963566 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) : (term17 _127719 u x) = (term65 _127719 u x).
Proof. exact (@lem6963564 (u x)). Qed.
Lemma lem6963569 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term58 _127719 v u x) : term65 _127719 u x.
Proof. exact (EQ_MP (@lem6963566 _127719 u x) (@lem6963518 _127719 v u x h1)). Qed.
Lemma lem6963572 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (@lem6963569 _127719 v u x h2 (@lem6963561 _127719 u x h1)). Qed.
Lemma lem6963573 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : term66.
Proof. exact (fun h0 : ~ False => @lem6963572 _127719 v u x h1 h2). Qed.
Lemma lem6963575 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6963576 : term66 = False.
Proof. exact (@lem6963575 False). Qed.
Lemma lem6963577 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963576) (@lem6963573 _127719 v u x h1 h2)). Qed.
Lemma lem6963579 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : v x) : v x.
Proof. exact (h1). Qed.
Lemma lem6963580 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : v x) : term63 _127719 v x.
Proof. exact (fun h0 : term17 _127719 v x => @lem6963579 _127719 v x h1). Qed.
Lemma lem6963582 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6963583 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) : (term63 _127719 v x) = (v x).
Proof. exact (@lem6963582 (v x)). Qed.
Lemma lem6963584 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : v x) : v x.
Proof. exact (EQ_MP (@lem6963583 _127719 v x) (@lem6963580 _127719 v x h1)). Qed.
Lemma lem6963587 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6963589 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) : (term17 _127719 v x) = (term65 _127719 v x).
Proof. exact (@lem6963587 (v x)). Qed.
Lemma lem6963592 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) : term65 _127719 v x.
Proof. exact (EQ_MP (@lem6963589 _127719 v x) (@lem6963526 _127719 v x h1)). Qed.
Lemma lem6963595 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) (h2 : v x) : False.
Proof. exact (@lem6963592 _127719 v x h1 (@lem6963584 _127719 v x h2)). Qed.
Lemma lem6963596 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) (h2 : v x) : term66.
Proof. exact (fun h0 : ~ False => @lem6963595 _127719 v x h1 h2). Qed.
Lemma lem6963598 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6963599 : term66 = False.
Proof. exact (@lem6963598 False). Qed.
Lemma lem6963600 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem6963599) (@lem6963596 _127719 v x h1 h2)). Qed.
Lemma lem6963602 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem6963603 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : term63 _127719 u x.
Proof. exact (fun h0 : term17 _127719 u x => @lem6963602 _127719 u x h1). Qed.
Lemma lem6963605 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6963606 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) : (term63 _127719 u x) = (u x).
Proof. exact (@lem6963605 (u x)). Qed.
Lemma lem6963607 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (EQ_MP (@lem6963606 _127719 u x) (@lem6963603 _127719 u x h1)). Qed.
Lemma lem6963610 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6963612 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) : (term17 _127719 u x) = (term65 _127719 u x).
Proof. exact (@lem6963610 (u x)). Qed.
Lemma lem6963615 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term58 _127719 v u x) : term65 _127719 u x.
Proof. exact (EQ_MP (@lem6963612 _127719 u x) (@lem6963530 _127719 v u x h1)). Qed.
Lemma lem6963618 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (@lem6963615 _127719 v u x h2 (@lem6963607 _127719 u x h1)). Qed.
Lemma lem6963619 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : term66.
Proof. exact (fun h0 : ~ False => @lem6963618 _127719 v u x h1 h2). Qed.
Lemma lem6963621 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6963622 : term66 = False.
Proof. exact (@lem6963621 False). Qed.
Lemma lem6963623 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963622) (@lem6963619 _127719 v u x h1 h2)). Qed.
Lemma lem6963625 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem6963626 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : term63 _127719 u x.
Proof. exact (fun h0 : term17 _127719 u x => @lem6963625 _127719 u x h1). Qed.
Lemma lem6963628 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6963629 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) : (term63 _127719 u x) = (u x).
Proof. exact (@lem6963628 (u x)). Qed.
Lemma lem6963630 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (EQ_MP (@lem6963629 _127719 u x) (@lem6963626 _127719 u x h1)). Qed.
Lemma lem6963633 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6963635 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) : (term17 _127719 u x) = (term65 _127719 u x).
Proof. exact (@lem6963633 (u x)). Qed.
Lemma lem6963638 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term58 _127719 v u x) : term65 _127719 u x.
Proof. exact (EQ_MP (@lem6963635 _127719 u x) (@lem6963536 _127719 v u x h1)). Qed.
Lemma lem6963641 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (@lem6963638 _127719 v u x h2 (@lem6963630 _127719 u x h1)). Qed.
Lemma lem6963642 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : term66.
Proof. exact (fun h0 : ~ False => @lem6963641 _127719 v u x h1 h2). Qed.
Lemma lem6963644 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6963645 : term66 = False.
Proof. exact (@lem6963644 False). Qed.
Lemma lem6963646 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963645) (@lem6963642 _127719 v u x h1 h2)). Qed.
Lemma lem6963648 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem6963649 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : term63 _127719 u x.
Proof. exact (fun h0 : term17 _127719 u x => @lem6963648 _127719 u x h1). Qed.
Lemma lem6963651 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6963652 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) : (term63 _127719 u x) = (u x).
Proof. exact (@lem6963651 (u x)). Qed.
Lemma lem6963653 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) (h1 : u x) : u x.
Proof. exact (EQ_MP (@lem6963652 _127719 u x) (@lem6963649 _127719 u x h1)). Qed.
Lemma lem6963656 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6963658 {_127719 : Type'} (u : _127719 -> Prop) (x : _127719) : (term17 _127719 u x) = (term65 _127719 u x).
Proof. exact (@lem6963656 (u x)). Qed.
Lemma lem6963661 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term55 _127719 v u x) : term65 _127719 u x.
Proof. exact (EQ_MP (@lem6963658 _127719 u x) (@lem6963542 _127719 v u x h1)). Qed.
Lemma lem6963664 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term55 _127719 v u x) : False.
Proof. exact (@lem6963661 _127719 v u x h2 (@lem6963653 _127719 u x h1)). Qed.
Lemma lem6963665 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term55 _127719 v u x) : term66.
Proof. exact (fun h0 : ~ False => @lem6963664 _127719 v u x h1 h2). Qed.
Lemma lem6963667 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6963668 : term66 = False.
Proof. exact (@lem6963667 False). Qed.
Lemma lem6963669 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term55 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963668) (@lem6963665 _127719 v u x h1 h2)). Qed.
Lemma lem6963671 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term18 _127719 v u x) : v x.
Proof. exact (proj1 (@lem6963438 _127719 v u x h1)). Qed.
Lemma lem6963672 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term18 _127719 v u x) : term63 _127719 v x.
Proof. exact (fun h0 : term17 _127719 v x => @lem6963671 _127719 v u x h1). Qed.
Lemma lem6963674 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6963675 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) : (term63 _127719 v x) = (v x).
Proof. exact (@lem6963674 (v x)). Qed.
Lemma lem6963676 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term18 _127719 v u x) : v x.
Proof. exact (EQ_MP (@lem6963675 _127719 v x) (@lem6963672 _127719 v u x h1)). Qed.
Lemma lem6963679 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6963681 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) : (term17 _127719 v x) = (term65 _127719 v x).
Proof. exact (@lem6963679 (v x)). Qed.
Lemma lem6963684 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term55 _127719 v u x) : term65 _127719 v x.
Proof. exact (EQ_MP (@lem6963681 _127719 v x) (@lem6963550 _127719 v u x h1)). Qed.
Lemma lem6963687 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term18 _127719 v u x) (h2 : term55 _127719 v u x) : False.
Proof. exact (@lem6963684 _127719 v u x h2 (@lem6963676 _127719 v u x h1)). Qed.
Lemma lem6963688 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term18 _127719 v u x) (h2 : term55 _127719 v u x) : term66.
Proof. exact (fun h0 : ~ False => @lem6963687 _127719 v u x h1 h2). Qed.
Lemma lem6963690 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6963691 : term66 = False.
Proof. exact (@lem6963690 False). Qed.
Lemma lem6963692 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term18 _127719 v u x) (h2 : term55 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963691) (@lem6963688 _127719 v u x h1 h2)). Qed.
Lemma lem6963693 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term55 _127719 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem6963669 _127719 v u x h1 h2) (fun h3 : False => @lem6963546 _127719 u x h1)). Qed.
Lemma lem6963694 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term55 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963693 _127719 v u x h1 h2) (@lem6963546 _127719 u x h1)). Qed.
Lemma lem6963695 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem6963646 _127719 v u x h1 h2) (fun h3 : False => @lem6963538 _127719 u x h1)). Qed.
Lemma lem6963696 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963695 _127719 v u x h1 h2) (@lem6963538 _127719 u x h1)). Qed.
Lemma lem6963697 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem6963623 _127719 v u x h1 h2) (fun h3 : False => @lem6963534 _127719 u x h1)). Qed.
Lemma lem6963698 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963697 _127719 v u x h1 h2) (@lem6963534 _127719 u x h1)). Qed.
Lemma lem6963699 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem6963698 _127719 v u x h1 h2) (fun h3 : False => @lem6963532 _127719 u x h1)). Qed.
Lemma lem6963700 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963699 _127719 v u x h1 h2) (@lem6963532 _127719 u x h1)). Qed.
Lemma lem6963701 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) (h2 : v x) : (v x) = False.
Proof. exact (prop_ext (fun h3 : v x => @lem6963600 _127719 v x h1 h2) (fun h3 : False => @lem6963528 _127719 v x h2)). Qed.
Lemma lem6963702 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem6963701 _127719 v x h1 h2) (@lem6963528 _127719 v x h2)). Qed.
Lemma lem6963703 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) (h2 : v x) : (term17 _127719 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _127719 v x => @lem6963702 _127719 v x h1 h2) (fun h3 : False => @lem6963526 _127719 v x h1)). Qed.
Lemma lem6963704 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem6963703 _127719 v x h1 h2) (@lem6963526 _127719 v x h1)). Qed.
Lemma lem6963705 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem6963577 _127719 v u x h1 h2) (fun h3 : False => @lem6963522 _127719 u x h1)). Qed.
Lemma lem6963706 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963705 _127719 v u x h1 h2) (@lem6963522 _127719 u x h1)). Qed.
Lemma lem6963707 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term55 _127719 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem6963694 _127719 v u x h1 h2) (fun h3 : False => @lem6963500 _127719 u x h1)). Qed.
Lemma lem6963708 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term55 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963707 _127719 v u x h1 h2) (@lem6963500 _127719 u x h1)). Qed.
Lemma lem6963709 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem6963696 _127719 v u x h1 h2) (fun h3 : False => @lem6963484 _127719 u x h1)). Qed.
Lemma lem6963710 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963709 _127719 v u x h1 h2) (@lem6963484 _127719 u x h1)). Qed.
Lemma lem6963711 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem6963700 _127719 v u x h1 h2) (fun h3 : False => @lem6963476 _127719 u x h1)). Qed.
Lemma lem6963712 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963711 _127719 v u x h1 h2) (@lem6963476 _127719 u x h1)). Qed.
Lemma lem6963713 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem6963712 _127719 v u x h1 h2) (fun h3 : False => @lem6963472 _127719 u x h1)). Qed.
Lemma lem6963714 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963713 _127719 v u x h1 h2) (@lem6963472 _127719 u x h1)). Qed.
Lemma lem6963715 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) (h2 : v x) : (v x) = False.
Proof. exact (prop_ext (fun h3 : v x => @lem6963704 _127719 v x h1 h2) (fun h3 : False => @lem6963464 _127719 v x h2)). Qed.
Lemma lem6963716 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem6963715 _127719 v x h1 h2) (@lem6963464 _127719 v x h2)). Qed.
Lemma lem6963717 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) (h2 : v x) : (term17 _127719 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _127719 v x => @lem6963716 _127719 v x h1 h2) (fun h3 : False => @lem6963460 _127719 v x h1)). Qed.
Lemma lem6963718 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem6963717 _127719 v x h1 h2) (@lem6963460 _127719 v x h1)). Qed.
Lemma lem6963719 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem6963706 _127719 v u x h1 h2) (fun h3 : False => @lem6963452 _127719 u x h1)). Qed.
Lemma lem6963720 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963719 _127719 v u x h1 h2) (@lem6963452 _127719 u x h1)). Qed.
Lemma lem6963721 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term55 _127719 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem6963708 _127719 v u x h1 h2) (fun h3 : False => @lem6963500 _127719 u x h1)). Qed.
Lemma lem6963722 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term55 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963721 _127719 v u x h1 h2) (@lem6963500 _127719 u x h1)). Qed.
Lemma lem6963723 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem6963710 _127719 v u x h1 h2) (fun h3 : False => @lem6963484 _127719 u x h1)). Qed.
Lemma lem6963724 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963723 _127719 v u x h1 h2) (@lem6963484 _127719 u x h1)). Qed.
Lemma lem6963725 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem6963714 _127719 v u x h1 h2) (fun h3 : False => @lem6963476 _127719 u x h1)). Qed.
Lemma lem6963726 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963725 _127719 v u x h1 h2) (@lem6963476 _127719 u x h1)). Qed.
Lemma lem6963727 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem6963726 _127719 v u x h1 h2) (fun h3 : False => @lem6963472 _127719 u x h1)). Qed.
Lemma lem6963728 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963727 _127719 v u x h1 h2) (@lem6963472 _127719 u x h1)). Qed.
Lemma lem6963729 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) (h2 : v x) : (v x) = False.
Proof. exact (prop_ext (fun h3 : v x => @lem6963718 _127719 v x h1 h2) (fun h3 : False => @lem6963464 _127719 v x h2)). Qed.
Lemma lem6963730 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem6963729 _127719 v x h1 h2) (@lem6963464 _127719 v x h2)). Qed.
Lemma lem6963731 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) (h2 : v x) : (term17 _127719 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _127719 v x => @lem6963730 _127719 v x h1 h2) (fun h3 : False => @lem6963460 _127719 v x h1)). Qed.
Lemma lem6963732 {_127719 : Type'} (v : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem6963731 _127719 v x h1 h2) (@lem6963460 _127719 v x h1)). Qed.
Lemma lem6963733 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem6963720 _127719 v u x h1 h2) (fun h3 : False => @lem6963452 _127719 u x h1)). Qed.
Lemma lem6963734 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963733 _127719 v u x h1 h2) (@lem6963452 _127719 u x h1)). Qed.
Lemma lem6963735 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term55 _127719 v u x) : False.
Proof. exact (or_elim (@lem6963433 _127719 v u x h1) (fun h0 : u x => @lem6963722 _127719 v u x h0 h1) (fun h0 : term18 _127719 v u x => @lem6963692 _127719 v u x h0 h1)). Qed.
Lemma lem6963736 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : u x) (h2 : term58 _127719 v u x) : False.
Proof. exact (or_elim (@lem6963424 _127719 v u x h2) (fun h0 : u x => @lem6963728 _127719 v u x h1 h2) (fun h0 : v x => @lem6963724 _127719 v u x h1 h2)). Qed.
Lemma lem6963737 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term17 _127719 v x) (h2 : term58 _127719 v u x) : False.
Proof. exact (or_elim (@lem6963424 _127719 v u x h2) (fun h0 : u x => @lem6963734 _127719 v u x h0 h2) (fun h0 : v x => @lem6963732 _127719 v x h1 h0)). Qed.
Lemma lem6963738 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term58 _127719 v u x) : False.
Proof. exact (or_elim (@lem6963425 _127719 v u x h1) (fun h0 : term17 _127719 v x => @lem6963737 _127719 v u x h0 h1) (fun h0 : u x => @lem6963736 _127719 v u x h0 h1)). Qed.
Lemma lem6963739 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term40 _127719 v u x) : False.
Proof. exact (or_elim (@lem6963420 _127719 v u x h1) (fun h0 : term58 _127719 v u x => @lem6963738 _127719 v u x h0) (fun h0 : term55 _127719 v u x => @lem6963735 _127719 v u x h0)). Qed.
Lemma lem6963740 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term40 _127719 v u x) : (term40 _127719 v u x) = False.
Proof. exact (prop_ext (fun h2 : term40 _127719 v u x => @lem6963739 _127719 v u x h1) (fun h2 : False => @lem6963300 _127719 v u x h1)). Qed.
Lemma lem6963741 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) (h1 : term40 _127719 v u x) : False.
Proof. exact (EQ_MP (@lem6963740 _127719 v u x h1) (@lem6963300 _127719 v u x h1)). Qed.
Lemma lem6963742 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : term39 _127719 v u x.
Proof. exact (fun h0 : term40 _127719 v u x => @lem6963741 _127719 v u x h0). Qed.
Lemma lem6963743 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (x : _127719) : (term7 _127719 u v x) = (term19 _127719 v u x).
Proof. exact (EQ_MP (@lem6963299 _127719 v u x) (@lem6963742 _127719 v u x)). Qed.
Lemma lem6963748 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : term22 _127719 v u.
Proof. exact (fun x : _127719 => @lem6963743 _127719 v u x). Qed.
Lemma lem6963753 {_127719 : Type'} (u : _127719 -> Prop) : term34 _127719 u.
Proof. exact (fun v : _127719 -> Prop => @lem6963748 _127719 v u). Qed.
Lemma lem6963758 {_127719 : Type'} : term38 _127719.
Proof. exact (fun u : _127719 -> Prop => @lem6963753 _127719 u). Qed.
Lemma lem6963759 {_127719 : Type'} : term37 _127719.
Proof. exact (EQ_MP (@lem6963295 _127719) (@lem6963758 _127719)). Qed.
Lemma lem6963760 {_127719 : Type'} (u : _127719 -> Prop) : term67 _127719 u.
Proof. exact (@lem6963759 _127719 u). Qed.
Lemma lem6963761 {_127719 : Type'} (u : _127719 -> Prop) : (term67 _127719 u) = (term33 _127719 u).
Proof. exact (eq_refl (term67 _127719 u)). Qed.
Lemma lem6963762 {_127719 : Type'} (u : _127719 -> Prop) : term33 _127719 u.
Proof. exact (EQ_MP (@lem6963761 _127719 u) (@lem6963760 _127719 u)). Qed.
Lemma lem6963763 {_127719 : Type'} (u : _127719 -> Prop) (v : _127719 -> Prop) : term68 _127719 u v.
Proof. exact (@lem6963762 _127719 u v). Qed.
Lemma lem6963764 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : (term68 _127719 u v) = (term24 _127719 v u).
Proof. exact (eq_refl (term68 _127719 u v)). Qed.
Lemma lem6963765 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : term24 _127719 v u.
Proof. exact (EQ_MP (@lem6963764 _127719 v u) (@lem6963763 _127719 u v)). Qed.
Lemma lem6963767 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : term24 _127719 v u.
Proof. exact (@lem6963196 _127719 v u (@lem6963765 _127719 v u)). Qed.
Lemma lem6963768 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (h1 : term25 _127719 v u) : False.
Proof. exact (@lem6963767 _127719 v u (@lem6963180 _127719 v u h1)). Qed.
Lemma lem6963769 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (h1 : term25 _127719 v u) : (term25 _127719 v u) = False.
Proof. exact (prop_ext (fun h2 : term25 _127719 v u => @lem6963768 _127719 v u h1) (fun h2 : False => @lem6963180 _127719 v u h1)). Qed.
Lemma lem6963770 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) (h1 : term25 _127719 v u) : False.
Proof. exact (EQ_MP (@lem6963769 _127719 v u h1) (@lem6963180 _127719 v u h1)). Qed.
Lemma lem6963771 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : term24 _127719 v u.
Proof. exact (fun h0 : term25 _127719 v u => @lem6963770 _127719 v u h0). Qed.
Lemma lem6963772 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : term22 _127719 v u.
Proof. exact (EQ_MP (@lem6963179 _127719 v u) (@lem6963771 _127719 v u)). Qed.
Lemma lem6963773 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : term2 _127719 v u.
Proof. exact (EQ_MP (@lem6963175 _127719 v u) (@lem6963772 _127719 v u)). Qed.
Lemma lem6963775 (t1 : Prop) : term69 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem6963776 (t1 : Prop) : (term69 t1) = (term70 t1).
Proof. exact (eq_refl (term69 t1)). Qed.
Lemma lem6963777 (t1 : Prop) : term70 t1.
Proof. exact (EQ_MP (@lem6963776 t1) (@lem6963775 t1)). Qed.
Lemma lem6963778 (t1 : Prop) (t2 : Prop) : term71 t1 t2.
Proof. exact (@lem6963777 t1 t2). Qed.
Lemma lem6963779 (t1 : Prop) (t2 : Prop) : (term71 t1 t2) = (term72 t1 t2).
Proof. exact (eq_refl (term71 t1 t2)). Qed.
Lemma lem6963780 (t1 : Prop) (t2 : Prop) : term72 t1 t2.
Proof. exact (EQ_MP (@lem6963779 t1 t2) (@lem6963778 t1 t2)). Qed.
Lemma lem6963781 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term73 t1 t2 t3.
Proof. exact (@lem6963780 t1 t2 t3). Qed.
Lemma lem6963782 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term73 t1 t2 t3) = ((term74 t1 t2 t3) = (term75 t1 t2 t3)).
Proof. exact (eq_refl (term73 t1 t2 t3)). Qed.
Lemma lem6963783 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term74 t1 t2 t3) = (term75 t1 t2 t3).
Proof. exact (EQ_MP (@lem6963782 t1 t2 t3) (@lem6963781 t1 t2 t3)). Qed.
Lemma lem6963784 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term75 t1 t2 t3) = (term74 t1 t2 t3).
Proof. exact (SYM (@lem6963783 t1 t2 t3)). Qed.
Lemma lem6963785 {A : Type'} (h1 : term76 A) : term76 A.
Proof. exact (h1). Qed.
Lemma lem6963786 {A : Type'} (f : A -> nat) (h1 : term76 A) : term77 A f.
Proof. exact (@lem6963785 A h1 f). Qed.
Lemma lem6963787 {A : Type'} (f : A -> nat) : (term77 A f) = (term78 A f).
Proof. exact (eq_refl (term77 A f)). Qed.
Lemma lem6963788 {A : Type'} (f : A -> nat) (h1 : term76 A) : term78 A f.
Proof. exact (EQ_MP (@lem6963787 A f) (@lem6963786 A f h1)). Qed.
Lemma lem6963789 {A : Type'} (f : A -> nat) (u : A -> Prop) (h1 : term76 A) : term79 A f u.
Proof. exact (@lem6963788 A f h1 u). Qed.
Lemma lem6963790 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term79 A f u) = (term80 A u f).
Proof. exact (eq_refl (term79 A f u)). Qed.
Lemma lem6963791 {A : Type'} (u : A -> Prop) (f : A -> nat) (h1 : term76 A) : term80 A u f.
Proof. exact (EQ_MP (@lem6963790 A u f) (@lem6963789 A f u h1)). Qed.
Lemma lem6963792 {A : Type'} (u : A -> Prop) (f : A -> nat) (v : A -> Prop) (h1 : term76 A) : term81 A u f v.
Proof. exact (@lem6963791 A u f h1 v). Qed.
Lemma lem6963793 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term81 A u f v) = (term82 A v u f).
Proof. exact (eq_refl (term81 A u f v)). Qed.
Lemma lem6963794 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term76 A) : term82 A v u f.
Proof. exact (EQ_MP (@lem6963793 A v u f) (@lem6963792 A u f v h1)). Qed.
Lemma lem6963795 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term83 A v u f) : term83 A v u f.
Proof. exact (h1). Qed.
Lemma lem6963796 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term76 A) (h2 : term83 A v u f) : (@nsum A v f) = (@nsum A u f).
Proof. exact (@lem6963794 A v u f h1 (@lem6963795 A v u f h2)). Qed.
Lemma lem6963797 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term83 A v u f) : term84 A v u f.
Proof. exact (fun h0 : term76 A => @lem6963796 A v u f h0 h1). Qed.
Lemma lem6963798 {A : Type'} (h1 : term76 A) : term76 A.
Proof. exact (h1). Qed.
Lemma lem6963799 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term76 A) (h2 : term83 A v u f) : (@nsum A v f) = (@nsum A u f).
Proof. exact (@lem6963797 A v u f h2 (@lem6963798 A h1)). Qed.
Lemma lem6963800 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term76 A) : term82 A v u f.
Proof. exact (fun h0 : term83 A v u f => @lem6963799 A v u f h1 h0). Qed.
Lemma lem6963801 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term76 A) : term85 A v u.
Proof. exact (fun f : A -> nat => @lem6963800 A v u f h1). Qed.
Lemma lem6963802 {A : Type'} (v : A -> Prop) (h1 : term76 A) : term86 A v.
Proof. exact (fun u : A -> Prop => @lem6963801 A v u h1). Qed.
Lemma lem6963803 {A : Type'} (h1 : term76 A) : term87 A.
Proof. exact (fun v : A -> Prop => @lem6963802 A v h1). Qed.
Lemma lem6963804 {A : Type'} : term88 A.
Proof. exact (fun h0 : term76 A => @lem6963803 A h0). Qed.
Lemma lem6963805 {A : Type'} : term87 A.
Proof. exact (@lem6963804 A (@lem6962131 A)). Qed.
Lemma lem6963806 {A : Type'} (v : A -> Prop) : term89 A v.
Proof. exact (@lem6963805 A v). Qed.
Lemma lem6963807 {A : Type'} (v : A -> Prop) : (term89 A v) = (term86 A v).
Proof. exact (eq_refl (term89 A v)). Qed.
Lemma lem6963808 {A : Type'} (v : A -> Prop) : term86 A v.
Proof. exact (EQ_MP (@lem6963807 A v) (@lem6963806 A v)). Qed.
Lemma lem6963809 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term90 A v u.
Proof. exact (@lem6963808 A v u). Qed.
Lemma lem6963810 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term90 A v u) = (term85 A v u).
Proof. exact (eq_refl (term90 A v u)). Qed.
Lemma lem6963811 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term85 A v u.
Proof. exact (EQ_MP (@lem6963810 A v u) (@lem6963809 A v u)). Qed.
Lemma lem6963812 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term91 A v u f.
Proof. exact (@lem6963811 A v u f). Qed.
Lemma lem6963813 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term91 A v u f) = (term82 A v u f).
Proof. exact (eq_refl (term91 A v u f)). Qed.
Lemma lem6963815 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term92 A v u f) : term92 A v u f.
Proof. exact (h1). Qed.
Lemma lem6963816 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) : term93 A v u f.
Proof. exact (h1). Qed.
Lemma lem6963817 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : @FINITE A u.
Proof. exact (h1). Qed.
Lemma lem6963821 {_127719 : Type'} (v : _127719 -> Prop) (u : _127719 -> Prop) : (@UNION _127719 u v) = (term1 _127719 v u).
Proof. exact (EQ_MP (@lem6963098 _127719 v u) (@lem6963773 _127719 v u)). Qed.
Lemma lem6963822 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (@UNION A u v) = (term1 A v u).
Proof. exact (@lem6963821 A v u). Qed.
Lemma lem6963823 {A : Type'} : (@nsum A) = (@nsum A).
Proof. exact (eq_refl (@nsum A)). Qed.
Lemma lem6963824 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term94 A u v) = (term95 A v u).
Proof. exact (MK_COMB (@lem6963823 A) (@lem6963822 A v u)). Qed.
Lemma lem6963825 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6963826 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term96 A u v f) = (term97 A v u f).
Proof. exact (MK_COMB (@lem6963824 A v u) (@lem6963825 A f)). Qed.
Lemma lem6963827 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6963828 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term98 A u v f) = (term99 A v u f).
Proof. exact (MK_COMB (@lem6963827) (@lem6963826 A v u f)). Qed.
Lemma lem6963829 {A : Type'} (u : A -> Prop) (f : A -> nat) : (@nsum A u f) = (@nsum A u f).
Proof. exact (eq_refl (@nsum A u f)). Qed.
Lemma lem6963830 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term96 A u v f) = (@nsum A u f)) = ((term97 A v u f) = (@nsum A u f)).
Proof. exact (MK_COMB (@lem6963828 A v u f) (@lem6963829 A u f)). Qed.
Lemma lem6963831 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term97 A v u f) = (@nsum A u f)) = ((term96 A u v f) = (@nsum A u f)).
Proof. exact (SYM (@lem6963830 A v u f)). Qed.
Lemma lem6963833 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term82 A v u f.
Proof. exact (EQ_MP (@lem6963813 A v u f) (@lem6963812 A v u f)). Qed.
Lemma lem6963834 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term82 A v u f.
Proof. exact (@lem6963833 A v u f). Qed.
Lemma lem6963835 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term100 A v u f.
Proof. exact (@lem6963834 A (term1 A v u) u f). Qed.
Lemma lem6963837 (p : Prop) : p = (term23 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6963838 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term101 A v u f) = (term102 A v u f).
Proof. exact (@lem6963837 (term101 A v u f)). Qed.
Lemma lem6963839 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term102 A v u f) = (term101 A v u f).
Proof. exact (SYM (@lem6963838 A v u f)). Qed.
Lemma lem6963840 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term103 A v u f) : term103 A v u f.
Proof. exact (h1). Qed.
Lemma lem6963841 {A : Type'} : term104 A.
Proof. exact (@lem3204949 A). Qed.
Lemma lem6963843 {A : Type'} : term105 A.
Proof. exact (@lem3205495 A). Qed.
Lemma lem6963845 {A : Type'} : term106 A.
Proof. exact (@lem3194148 A). Qed.
Lemma lem6963849 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term107 A v u f) : term107 A v u f.
Proof. exact (h1). Qed.
Lemma lem6963850 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term108 A v u f.
Proof. exact (fun h0 : term107 A v u f => @lem6963849 A v u f h0). Qed.
Lemma lem6963851 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term108 A v u f) : term108 A v u f.
Proof. exact (h1). Qed.
Lemma lem6963852 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term107 A v u f) : term107 A v u f.
Proof. exact (h1). Qed.
Lemma lem6963853 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term107 A v u f) (h2 : term108 A v u f) : term107 A v u f.
Proof. exact (@lem6963851 A v u f h2 (@lem6963852 A v u f h1)). Qed.
Lemma lem6963854 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term107 A v u f) : term109 A v u f.
Proof. exact (fun h0 : term108 A v u f => @lem6963853 A v u f h1 h0). Qed.
Lemma lem6963855 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term108 A v u f) : term108 A v u f.
Proof. exact (h1). Qed.
Lemma lem6963856 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term107 A v u f) (h2 : term108 A v u f) : term107 A v u f.
Proof. exact (@lem6963854 A v u f h1 (@lem6963855 A v u f h2)). Qed.
Lemma lem6963857 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term108 A v u f) : term108 A v u f.
Proof. exact (fun h0 : term107 A v u f => @lem6963856 A v u f h0 h1). Qed.
Lemma lem6963858 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term110 A v u f.
Proof. exact (fun h0 : term108 A v u f => @lem6963857 A v u f h0). Qed.
Lemma lem6963861 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term108 A v u f.
Proof. exact (@lem6963858 A v u f (@lem6963850 A v u f)). Qed.
Lemma lem6963862 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term108 A v u f.
Proof. exact (@lem6963861 A v u f). Qed.
Lemma lem6963932 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6963933 {A : Type'} : (term111 A) = (term112 A).
Proof. exact (@lem6963932 (term104 A)). Qed.
Lemma lem6963948 {A : Type'} : (term113 A) = (term113 A).
Proof. exact (eq_refl (term113 A)). Qed.
Lemma lem6963949 {A : Type'} : (term114 A) = (term115 A).
Proof. exact (MK_COMB (@lem6963948 A) (@lem6963933 A)). Qed.
Lemma lem6963952 {A : Type'} : (term116 A) = (term116 A).
Proof. exact (eq_refl (term116 A)). Qed.
Lemma lem6963953 {A : Type'} : (term117 A) = (term118 A).
Proof. exact (MK_COMB (@lem6963952 A) (@lem6963949 A)). Qed.
Lemma lem6963956 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term119 A v u f) = (term119 A v u f).
Proof. exact (eq_refl (term119 A v u f)). Qed.
Lemma lem6963957 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term120 A v u f) = (term121 A v u f).
Proof. exact (MK_COMB (@lem6963956 A v u f) (@lem6963953 A)). Qed.
Lemma lem6963960 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term122 A v u f) = (term122 A v u f).
Proof. exact (eq_refl (term122 A v u f)). Qed.
Lemma lem6963961 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term123 A v u f) = (term124 A v u f).
Proof. exact (MK_COMB (@lem6963960 A v u f) (@lem6963957 A v u f)). Qed.
Lemma lem6963964 {A : Type'} (u : A -> Prop) : (term125 A u) = (term125 A u).
Proof. exact (eq_refl (term125 A u)). Qed.
Lemma lem6963965 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term107 A v u f) = (term126 A v u f).
Proof. exact (MK_COMB (@lem6963964 A u) (@lem6963961 A v u f)). Qed.
Lemma lem6963968 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term127 A u f) = (term128 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6963965 A v u f)). Qed.
Lemma lem6963969 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6963970 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term129 A u f) = (term130 A u f).
Proof. exact (MK_COMB (@lem6963969 A) (@lem6963968 A u f)). Qed.
Lemma lem6963975 {A : Type'} (f : A -> nat) : (term131 A f) = (term132 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6963970 A u f)). Qed.
Lemma lem6963976 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6963977 {A : Type'} (f : A -> nat) : (term133 A f) = (term134 A f).
Proof. exact (MK_COMB (@lem6963976 A) (@lem6963975 A f)). Qed.
Lemma lem6963982 {A : Type'} : (term135 A) = (term136 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6963977 A f)). Qed.
Lemma lem6963983 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6963992 {A : Type'} : (term137 A) = (term138 A).
Proof. exact (MK_COMB (@lem6963983 A) (@lem6963982 A)). Qed.
Lemma lem6964001 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term3 A x s t) = (term4 A s x t)) = ((term3 A x s t) = (term4 A s x t)).
Proof. exact (eq_refl ((term3 A x s t) = (term4 A s x t))). Qed.
Lemma lem6964002 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term139 A s t) = (term139 A s t).
Proof. exact (fun_ext (fun x : A => @lem6964001 A s x t)). Qed.
Lemma lem6964003 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6964004 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term140 A s t) = (term140 A s t).
Proof. exact (MK_COMB (@lem6964003 A) (@lem6964002 A s t)). Qed.
Lemma lem6964005 {A : Type'} (s : A -> Prop) : (term141 A s) = (term141 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6964004 A s t)). Qed.
Lemma lem6964006 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964007 {A : Type'} (s : A -> Prop) : (term142 A s) = (term142 A s).
Proof. exact (MK_COMB (@lem6964006 A) (@lem6964005 A s)). Qed.
Lemma lem6964008 {A : Type'} : (term143 A) = (term143 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6964007 A s)). Qed.
Lemma lem6964009 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964010 {A : Type'} : (term104 A) = (term104 A).
Proof. exact (MK_COMB (@lem6964009 A) (@lem6964008 A)). Qed.
Lemma lem6964011 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6964012 {A : Type'} : (term112 A) = (term112 A).
Proof. exact (MK_COMB (@lem6964011) (@lem6964010 A)). Qed.
Lemma lem6964023 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term12 A x s t) = (term13 A s x t)) = ((term12 A x s t) = (term13 A s x t)).
Proof. exact (eq_refl ((term12 A x s t) = (term13 A s x t))). Qed.
Lemma lem6964024 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term144 A s t) = (term144 A s t).
Proof. exact (fun_ext (fun x : A => @lem6964023 A s x t)). Qed.
Lemma lem6964025 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6964026 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term145 A s t) = (term145 A s t).
Proof. exact (MK_COMB (@lem6964025 A) (@lem6964024 A s t)). Qed.
Lemma lem6964027 {A : Type'} (s : A -> Prop) : (term146 A s) = (term146 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6964026 A s t)). Qed.
Lemma lem6964028 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964029 {A : Type'} (s : A -> Prop) : (term147 A s) = (term147 A s).
Proof. exact (MK_COMB (@lem6964028 A) (@lem6964027 A s)). Qed.
Lemma lem6964030 {A : Type'} : (term148 A) = (term148 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6964029 A s)). Qed.
Lemma lem6964031 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964032 {A : Type'} : (term105 A) = (term105 A).
Proof. exact (MK_COMB (@lem6964031 A) (@lem6964030 A)). Qed.
Lemma lem6964033 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6964034 {A : Type'} : (term113 A) = (term113 A).
Proof. exact (MK_COMB (@lem6964033) (@lem6964032 A)). Qed.
Lemma lem6964035 {A : Type'} : (term115 A) = (term115 A).
Proof. exact (MK_COMB (@lem6964034 A) (@lem6964012 A)). Qed.
Lemma lem6964040 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term149 A s x t) = (term149 A s x t).
Proof. exact (eq_refl (term149 A s x t)). Qed.
Lemma lem6964041 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term150 A s t) = (term150 A s t).
Proof. exact (fun_ext (fun x : A => @lem6964040 A s x t)). Qed.
Lemma lem6964042 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6964043 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term151 A s t) = (term151 A s t).
Proof. exact (MK_COMB (@lem6964042 A) (@lem6964041 A s t)). Qed.
Lemma lem6964046 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term152 A s t) = (term152 A s t).
Proof. exact (eq_refl (term152 A s t)). Qed.
Lemma lem6964047 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term151 A s t)) = ((@SUBSET A s t) = (term151 A s t)).
Proof. exact (MK_COMB (@lem6964046 A s t) (@lem6964043 A s t)). Qed.
Lemma lem6964048 {A : Type'} (s : A -> Prop) : (term153 A s) = (term153 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6964047 A s t)). Qed.
Lemma lem6964049 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964050 {A : Type'} (s : A -> Prop) : (term154 A s) = (term154 A s).
Proof. exact (MK_COMB (@lem6964049 A) (@lem6964048 A s)). Qed.
Lemma lem6964051 {A : Type'} : (term155 A) = (term155 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6964050 A s)). Qed.
Lemma lem6964052 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964053 {A : Type'} : (term106 A) = (term106 A).
Proof. exact (MK_COMB (@lem6964052 A) (@lem6964051 A)). Qed.
Lemma lem6964054 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6964055 {A : Type'} : (term116 A) = (term116 A).
Proof. exact (MK_COMB (@lem6964054) (@lem6964053 A)). Qed.
Lemma lem6964056 {A : Type'} : (term118 A) = (term118 A).
Proof. exact (MK_COMB (@lem6964055 A) (@lem6964035 A)). Qed.
Lemma lem6964067 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term156 A v u f x) = (term156 A v u f x).
Proof. exact (eq_refl (term156 A v u f x)). Qed.
Lemma lem6964068 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term157 A v u f) = (term157 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6964067 A v u f x)). Qed.
Lemma lem6964069 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6964070 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term158 A v u f) = (term158 A v u f).
Proof. exact (MK_COMB (@lem6964069 A) (@lem6964068 A v u f)). Qed.
Lemma lem6964073 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term159 A v u) = (term159 A v u).
Proof. exact (eq_refl (term159 A v u)). Qed.
Lemma lem6964074 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term101 A v u f) = (term101 A v u f).
Proof. exact (MK_COMB (@lem6964073 A v u) (@lem6964070 A v u f)). Qed.
Lemma lem6964075 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6964076 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term103 A v u f) = (term103 A v u f).
Proof. exact (MK_COMB (@lem6964075) (@lem6964074 A v u f)). Qed.
Lemma lem6964077 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6964078 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term119 A v u f) = (term119 A v u f).
Proof. exact (MK_COMB (@lem6964077) (@lem6964076 A v u f)). Qed.
Lemma lem6964079 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term121 A v u f) = (term121 A v u f).
Proof. exact (MK_COMB (@lem6964078 A v u f) (@lem6964056 A)). Qed.
Lemma lem6964090 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term160 A v u f x) = (term160 A v u f x).
Proof. exact (eq_refl (term160 A v u f x)). Qed.
Lemma lem6964091 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term161 A v u f) = (term161 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6964090 A v u f x)). Qed.
Lemma lem6964092 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6964093 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term93 A v u f) = (term93 A v u f).
Proof. exact (MK_COMB (@lem6964092 A) (@lem6964091 A v u f)). Qed.
Lemma lem6964094 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6964095 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term122 A v u f) = (term122 A v u f).
Proof. exact (MK_COMB (@lem6964094) (@lem6964093 A v u f)). Qed.
Lemma lem6964096 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term124 A v u f) = (term124 A v u f).
Proof. exact (MK_COMB (@lem6964095 A v u f) (@lem6964079 A v u f)). Qed.
Lemma lem6964099 {A : Type'} (u : A -> Prop) : (term125 A u) = (term125 A u).
Proof. exact (eq_refl (term125 A u)). Qed.
Lemma lem6964100 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term126 A v u f) = (term126 A v u f).
Proof. exact (MK_COMB (@lem6964099 A u) (@lem6964096 A v u f)). Qed.
Lemma lem6964101 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term128 A u f) = (term128 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6964100 A v u f)). Qed.
Lemma lem6964102 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964103 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term130 A u f) = (term130 A u f).
Proof. exact (MK_COMB (@lem6964102 A) (@lem6964101 A u f)). Qed.
Lemma lem6964104 {A : Type'} (f : A -> nat) : (term132 A f) = (term132 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6964103 A u f)). Qed.
Lemma lem6964105 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964106 {A : Type'} (f : A -> nat) : (term134 A f) = (term134 A f).
Proof. exact (MK_COMB (@lem6964105 A) (@lem6964104 A f)). Qed.
Lemma lem6964107 {A : Type'} : (term136 A) = (term136 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6964106 A f)). Qed.
Lemma lem6964108 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6964109 {A : Type'} : (term138 A) = (term138 A).
Proof. exact (MK_COMB (@lem6964108 A) (@lem6964107 A)). Qed.
Lemma lem6964222 {A : Type'} : (term137 A) = (term138 A).
Proof. exact (TRANS (@lem6963992 A) (@lem6964109 A)). Qed.
Lemma lem6964223 {A : Type'} : (term138 A) = (term137 A).
Proof. exact (SYM (@lem6964222 A)). Qed.
Lemma lem6964225 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) : term93 A v u f.
Proof. exact (h1). Qed.
Lemma lem6964226 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term103 A v u f) : term103 A v u f.
Proof. exact (h1). Qed.
Lemma lem6964227 {A : Type'} (h1 : term106 A) : term106 A.
Proof. exact (h1). Qed.
Lemma lem6964228 {A : Type'} (h1 : term105 A) : term105 A.
Proof. exact (h1). Qed.
Lemma lem6964229 {A : Type'} (h1 : term104 A) : term104 A.
Proof. exact (h1). Qed.
Lemma lem6964239 {A : Type'} (x : A) (u : A -> Prop) : (term162 A x u) = (@IN A x u).
Proof. exact (@lem16933 (@IN A x u)). Qed.
Lemma lem6964241 {A : Type'} (x : A) (v : A -> Prop) : (term163 A x v) = (term163 A x v).
Proof. exact (eq_refl (term163 A x v)). Qed.
Lemma lem6964242 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term164 A v x u) = (term165 A v x u).
Proof. exact (MK_COMB (@lem6964241 A x v) (@lem6964239 A x u)). Qed.
Lemma lem6964243 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term166 A v x u) = (term164 A v x u).
Proof. exact (@lem17045 (@IN A x v) (term16 A x u)). Qed.
Lemma lem6964244 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term166 A v x u) = (term165 A v x u).
Proof. exact (TRANS (@lem6964243 A v x u) (@lem6964242 A v x u)). Qed.
Lemma lem6964245 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((f x) = (NUMERAL 0)).
Proof. exact (eq_refl ((f x) = (NUMERAL 0))). Qed.
Lemma lem6964246 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6964247 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term167 A v x u) = (term168 A v x u).
Proof. exact (MK_COMB (@lem6964246) (@lem6964244 A v x u)). Qed.
Lemma lem6964248 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term169 A v u f x) = (term170 A v u f x).
Proof. exact (MK_COMB (@lem6964247 A v x u) (@lem6964245 A f x)). Qed.
Lemma lem6964249 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term160 A v u f x) = (term169 A v u f x).
Proof. exact (@lem17265 (term13 A v x u) ((f x) = (NUMERAL 0))). Qed.
Lemma lem6964250 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term160 A v u f x) = (term170 A v u f x).
Proof. exact (TRANS (@lem6964249 A v u f x) (@lem6964248 A v u f x)). Qed.
Lemma lem6964251 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term161 A v u f) = (term171 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6964250 A v u f x)). Qed.
Lemma lem6964252 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6964305 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term93 A v u f) = (term172 A v u f).
Proof. exact (MK_COMB (@lem6964252 A) (@lem6964251 A v u f)). Qed.
Lemma lem6964306 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) : term172 A v u f.
Proof. exact (EQ_MP (@lem6964305 A v u f) (@lem6964225 A v u f h1)). Qed.
Lemma lem6964318 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term173 A v u f x) = (term174 A v u f x).
Proof. exact (@lem17362 (term175 A v x u) ((f x) = (NUMERAL 0))). Qed.
Lemma lem6964319 {A : Type'} (P : A -> Prop) : (term176 A P) = (term177 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6964320 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term178 A v u f) = (term179 A v u f).
Proof. exact (@lem6964319 A (term157 A v u f)). Qed.
Lemma lem6964321 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term180 A v u f x) = (term156 A v u f x).
Proof. exact (eq_refl (term180 A v u f x)). Qed.
Lemma lem6964322 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6964323 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term181 A v u f x) = (term173 A v u f x).
Proof. exact (MK_COMB (@lem6964322) (@lem6964321 A v u f x)). Qed.
Lemma lem6964324 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term181 A v u f x) = (term174 A v u f x).
Proof. exact (TRANS (@lem6964323 A v u f x) (@lem6964318 A v u f x)). Qed.
Lemma lem6964325 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term182 A v u f) = (term183 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6964324 A v u f x)). Qed.
Lemma lem6964326 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6964327 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term179 A v u f) = (term184 A v u f).
Proof. exact (MK_COMB (@lem6964326 A) (@lem6964325 A v u f)). Qed.
Lemma lem6964328 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term178 A v u f) = (term184 A v u f).
Proof. exact (TRANS (@lem6964320 A v u f) (@lem6964327 A v u f)). Qed.
Lemma lem6964330 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term185 A v u) = (term185 A v u).
Proof. exact (eq_refl (term185 A v u)). Qed.
Lemma lem6964331 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term186 A v u f) = (term187 A v u f).
Proof. exact (MK_COMB (@lem6964330 A v u) (@lem6964328 A v u f)). Qed.
Lemma lem6964332 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term103 A v u f) = (term186 A v u f).
Proof. exact (@lem17045 (term188 A v u) (term158 A v u f)). Qed.
Lemma lem6964333 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term103 A v u f) = (term187 A v u f).
Proof. exact (TRANS (@lem6964332 A v u f) (@lem6964331 A v u f)). Qed.
Lemma lem6964384 {A : Type'} (P : Prop) (Q : A -> Prop) : (term189 A P Q) = (term190 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6964385 {A : Type'} (P : Prop) (Q : A -> Prop) : (term189 A P Q) = (term190 A P Q).
Proof. exact (@lem6964384 A P Q). Qed.
Lemma lem6964386 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term191 A v u f) = (term192 A v u f).
Proof. exact (@lem6964385 A (term193 A v u) (term183 A v u f)). Qed.
Lemma lem6964387 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term194 A v u f x) = (term174 A v u f x).
Proof. exact (eq_refl (term194 A v u f x)). Qed.
Lemma lem6964388 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term195 A v u f) = (term183 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6964387 A v u f x)). Qed.
Lemma lem6964389 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6964390 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term196 A v u f) = (term184 A v u f).
Proof. exact (MK_COMB (@lem6964389 A) (@lem6964388 A v u f)). Qed.
Lemma lem6964391 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term185 A v u) = (term185 A v u).
Proof. exact (eq_refl (term185 A v u)). Qed.
Lemma lem6964392 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term191 A v u f) = (term187 A v u f).
Proof. exact (MK_COMB (@lem6964391 A v u) (@lem6964390 A v u f)). Qed.
Lemma lem6964393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6964394 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term197 A v u f) = (term198 A v u f).
Proof. exact (MK_COMB (@lem6964393) (@lem6964392 A v u f)). Qed.
Lemma lem6964395 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term194 A v u f x) = (term174 A v u f x).
Proof. exact (eq_refl (term194 A v u f x)). Qed.
Lemma lem6964396 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term185 A v u) = (term185 A v u).
Proof. exact (eq_refl (term185 A v u)). Qed.
Lemma lem6964397 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term199 A v u f x) = (term200 A v u f x).
Proof. exact (MK_COMB (@lem6964396 A v u) (@lem6964395 A v u f x)). Qed.
Lemma lem6964398 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term201 A v u f) = (term202 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6964397 A v u f x)). Qed.
Lemma lem6964399 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6964400 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term192 A v u f) = (term203 A v u f).
Proof. exact (MK_COMB (@lem6964399 A) (@lem6964398 A v u f)). Qed.
Lemma lem6964401 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term191 A v u f) = (term192 A v u f)) = ((term187 A v u f) = (term203 A v u f)).
Proof. exact (MK_COMB (@lem6964394 A v u f) (@lem6964400 A v u f)). Qed.
Lemma lem6964403 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term187 A v u f) = (term203 A v u f).
Proof. exact (EQ_MP (@lem6964401 A v u f) (@lem6964386 A v u f)). Qed.
Lemma lem6964404 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term103 A v u f) = (term203 A v u f).
Proof. exact (TRANS (@lem6964333 A v u f) (@lem6964403 A v u f)). Qed.
Lemma lem6964405 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term103 A v u f) : term203 A v u f.
Proof. exact (EQ_MP (@lem6964404 A v u f) (@lem6964226 A v u f h1)). Qed.
Lemma lem6964416 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term204 A s x t) = (term13 A s x t).
Proof. exact (@lem17362 (@IN A x s) (@IN A x t)). Qed.
Lemma lem6964421 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term149 A s x t) = (term165 A s x t).
Proof. exact (@lem17265 (@IN A x s) (@IN A x t)). Qed.
Lemma lem6964422 {A : Type'} (P : A -> Prop) : (term176 A P) = (term177 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6964423 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term205 A s t) = (term206 A s t).
Proof. exact (@lem6964422 A (term150 A s t)). Qed.
Lemma lem6964424 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term207 A s t x) = (term149 A s x t).
Proof. exact (eq_refl (term207 A s t x)). Qed.
Lemma lem6964425 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6964426 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term208 A s t x) = (term204 A s x t).
Proof. exact (MK_COMB (@lem6964425) (@lem6964424 A s x t)). Qed.
Lemma lem6964427 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term208 A s t x) = (term13 A s x t).
Proof. exact (TRANS (@lem6964426 A s x t) (@lem6964416 A s x t)). Qed.
Lemma lem6964428 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term209 A s t) = (term210 A s t).
Proof. exact (fun_ext (fun x : A => @lem6964427 A s x t)). Qed.
Lemma lem6964429 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6964430 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term206 A s t) = (term211 A s t).
Proof. exact (MK_COMB (@lem6964429 A) (@lem6964428 A s t)). Qed.
Lemma lem6964431 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term205 A s t) = (term211 A s t).
Proof. exact (TRANS (@lem6964423 A s t) (@lem6964430 A s t)). Qed.
Lemma lem6964432 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term150 A s t) = (term212 A s t).
Proof. exact (fun_ext (fun x : A => @lem6964421 A s x t)). Qed.
Lemma lem6964433 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6964434 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term151 A s t) = (term213 A s t).
Proof. exact (MK_COMB (@lem6964433 A) (@lem6964432 A s t)). Qed.
Lemma lem6964436 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term214 A s t) = (term214 A s t).
Proof. exact (eq_refl (term214 A s t)). Qed.
Lemma lem6964437 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term215 A s t) = (term216 A s t).
Proof. exact (MK_COMB (@lem6964436 A s t) (@lem6964434 A s t)). Qed.
Lemma lem6964439 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term217 A s t) = (term217 A s t).
Proof. exact (eq_refl (term217 A s t)). Qed.
Lemma lem6964440 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term218 A s t) = (term219 A s t).
Proof. exact (MK_COMB (@lem6964439 A s t) (@lem6964431 A s t)). Qed.
Lemma lem6964441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6964442 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term220 A s t) = (term221 A s t).
Proof. exact (MK_COMB (@lem6964441) (@lem6964440 A s t)). Qed.
Lemma lem6964443 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term222 A s t) = (term223 A s t).
Proof. exact (MK_COMB (@lem6964442 A s t) (@lem6964437 A s t)). Qed.
Lemma lem6964444 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term151 A s t)) = (term222 A s t).
Proof. exact (@lem17784 (@SUBSET A s t) (term151 A s t)). Qed.
Lemma lem6964445 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term151 A s t)) = (term223 A s t).
Proof. exact (TRANS (@lem6964444 A s t) (@lem6964443 A s t)). Qed.
Lemma lem6964446 {A : Type'} (s : A -> Prop) : (term153 A s) = (term224 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6964445 A s t)). Qed.
Lemma lem6964447 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964448 {A : Type'} (s : A -> Prop) : (term154 A s) = (term225 A s).
Proof. exact (MK_COMB (@lem6964447 A) (@lem6964446 A s)). Qed.
Lemma lem6964449 {A : Type'} : (term155 A) = (term226 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6964448 A s)). Qed.
Lemma lem6964450 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964451 {A : Type'} : (term106 A) = (term227 A).
Proof. exact (MK_COMB (@lem6964450 A) (@lem6964449 A)). Qed.
Lemma lem6964457 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6964458 {A : Type'} (P : type686 A) (Q : type686 A) : (term230 A P Q) = (term231 A P Q).
Proof. exact (@lem6964457 (A -> Prop) P Q). Qed.
Lemma lem6964459 {A : Type'} (s : A -> Prop) : (term232 A s) = (term233 A s).
Proof. exact (@lem6964458 A (term234 A s) (term235 A s)). Qed.
Lemma lem6964460 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term236 A s t) = (term219 A s t).
Proof. exact (eq_refl (term236 A s t)). Qed.
Lemma lem6964461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6964462 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term237 A s t) = (term221 A s t).
Proof. exact (MK_COMB (@lem6964461) (@lem6964460 A s t)). Qed.
Lemma lem6964463 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term238 A s t) = (term216 A s t).
Proof. exact (eq_refl (term238 A s t)). Qed.
Lemma lem6964464 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term239 A s t) = (term223 A s t).
Proof. exact (MK_COMB (@lem6964462 A s t) (@lem6964463 A s t)). Qed.
Lemma lem6964465 {A : Type'} (s : A -> Prop) : (term240 A s) = (term224 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6964464 A s t)). Qed.
Lemma lem6964466 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964467 {A : Type'} (s : A -> Prop) : (term232 A s) = (term225 A s).
Proof. exact (MK_COMB (@lem6964466 A) (@lem6964465 A s)). Qed.
Lemma lem6964468 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6964469 {A : Type'} (s : A -> Prop) : (term241 A s) = (term242 A s).
Proof. exact (MK_COMB (@lem6964468) (@lem6964467 A s)). Qed.
Lemma lem6964470 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term236 A s t) = (term219 A s t).
Proof. exact (eq_refl (term236 A s t)). Qed.
Lemma lem6964471 {A : Type'} (s : A -> Prop) : (term243 A s) = (term234 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6964470 A s t)). Qed.
Lemma lem6964472 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964473 {A : Type'} (s : A -> Prop) : (term244 A s) = (term245 A s).
Proof. exact (MK_COMB (@lem6964472 A) (@lem6964471 A s)). Qed.
Lemma lem6964474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6964475 {A : Type'} (s : A -> Prop) : (term246 A s) = (term247 A s).
Proof. exact (MK_COMB (@lem6964474) (@lem6964473 A s)). Qed.
Lemma lem6964476 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term238 A s t) = (term216 A s t).
Proof. exact (eq_refl (term238 A s t)). Qed.
Lemma lem6964477 {A : Type'} (s : A -> Prop) : (term248 A s) = (term235 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6964476 A s t)). Qed.
Lemma lem6964478 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964479 {A : Type'} (s : A -> Prop) : (term249 A s) = (term250 A s).
Proof. exact (MK_COMB (@lem6964478 A) (@lem6964477 A s)). Qed.
Lemma lem6964480 {A : Type'} (s : A -> Prop) : (term233 A s) = (term251 A s).
Proof. exact (MK_COMB (@lem6964475 A s) (@lem6964479 A s)). Qed.
Lemma lem6964481 {A : Type'} (s : A -> Prop) : ((term232 A s) = (term233 A s)) = ((term225 A s) = (term251 A s)).
Proof. exact (MK_COMB (@lem6964469 A s) (@lem6964480 A s)). Qed.
Lemma lem6964482 {A : Type'} (s : A -> Prop) : (term225 A s) = (term251 A s).
Proof. exact (EQ_MP (@lem6964481 A s) (@lem6964459 A s)). Qed.
Lemma lem6964675 {A : Type'} : (term226 A) = (term252 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6964482 A s)). Qed.
Lemma lem6964676 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964677 {A : Type'} : (term227 A) = (term253 A).
Proof. exact (MK_COMB (@lem6964676 A) (@lem6964675 A)). Qed.
Lemma lem6964679 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6964680 {A : Type'} (P : type686 A) (Q : type686 A) : (term230 A P Q) = (term231 A P Q).
Proof. exact (@lem6964679 (A -> Prop) P Q). Qed.
Lemma lem6964681 {A : Type'} : (term254 A) = (term255 A).
Proof. exact (@lem6964680 A (term256 A) (term257 A)). Qed.
Lemma lem6964682 {A : Type'} (s : A -> Prop) : (term258 A s) = (term245 A s).
Proof. exact (eq_refl (term258 A s)). Qed.
Lemma lem6964683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6964684 {A : Type'} (s : A -> Prop) : (term259 A s) = (term247 A s).
Proof. exact (MK_COMB (@lem6964683) (@lem6964682 A s)). Qed.
Lemma lem6964685 {A : Type'} (s : A -> Prop) : (term260 A s) = (term250 A s).
Proof. exact (eq_refl (term260 A s)). Qed.
Lemma lem6964686 {A : Type'} (s : A -> Prop) : (term261 A s) = (term251 A s).
Proof. exact (MK_COMB (@lem6964684 A s) (@lem6964685 A s)). Qed.
Lemma lem6964687 {A : Type'} : (term262 A) = (term252 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6964686 A s)). Qed.
Lemma lem6964688 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964689 {A : Type'} : (term254 A) = (term253 A).
Proof. exact (MK_COMB (@lem6964688 A) (@lem6964687 A)). Qed.
Lemma lem6964690 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6964691 {A : Type'} : (term263 A) = (term264 A).
Proof. exact (MK_COMB (@lem6964690) (@lem6964689 A)). Qed.
Lemma lem6964692 {A : Type'} (s : A -> Prop) : (term258 A s) = (term245 A s).
Proof. exact (eq_refl (term258 A s)). Qed.
Lemma lem6964693 {A : Type'} : (term265 A) = (term256 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6964692 A s)). Qed.
Lemma lem6964694 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964695 {A : Type'} : (term266 A) = (term267 A).
Proof. exact (MK_COMB (@lem6964694 A) (@lem6964693 A)). Qed.
Lemma lem6964696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6964697 {A : Type'} : (term268 A) = (term269 A).
Proof. exact (MK_COMB (@lem6964696) (@lem6964695 A)). Qed.
Lemma lem6964698 {A : Type'} (s : A -> Prop) : (term260 A s) = (term250 A s).
Proof. exact (eq_refl (term260 A s)). Qed.
Lemma lem6964699 {A : Type'} : (term270 A) = (term257 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6964698 A s)). Qed.
Lemma lem6964700 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964701 {A : Type'} : (term271 A) = (term272 A).
Proof. exact (MK_COMB (@lem6964700 A) (@lem6964699 A)). Qed.
Lemma lem6964702 {A : Type'} : (term255 A) = (term273 A).
Proof. exact (MK_COMB (@lem6964697 A) (@lem6964701 A)). Qed.
Lemma lem6964703 {A : Type'} : ((term254 A) = (term255 A)) = ((term253 A) = (term273 A)).
Proof. exact (MK_COMB (@lem6964691 A) (@lem6964702 A)). Qed.
Lemma lem6964704 {A : Type'} : (term253 A) = (term273 A).
Proof. exact (EQ_MP (@lem6964703 A) (@lem6964681 A)). Qed.
Lemma lem6964905 {A : Type'} : (term227 A) = (term273 A).
Proof. exact (TRANS (@lem6964677 A) (@lem6964704 A)). Qed.
Lemma lem6964907 {A : Type'} (P : Prop) (Q : A -> Prop) : (term189 A P Q) = (term190 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6964908 {A : Type'} (P : Prop) (Q : A -> Prop) : (term189 A P Q) = (term190 A P Q).
Proof. exact (@lem6964907 A P Q). Qed.
Lemma lem6964909 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term274 A s t) = (term275 A s t).
Proof. exact (@lem6964908 A (@SUBSET A s t) (term210 A s t)). Qed.
Lemma lem6964910 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term276 A s t x) = (term13 A s x t).
Proof. exact (eq_refl (term276 A s t x)). Qed.
Lemma lem6964911 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term277 A s t) = (term210 A s t).
Proof. exact (fun_ext (fun x : A => @lem6964910 A s x t)). Qed.
Lemma lem6964912 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6964913 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term278 A s t) = (term211 A s t).
Proof. exact (MK_COMB (@lem6964912 A) (@lem6964911 A s t)). Qed.
Lemma lem6964914 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term217 A s t) = (term217 A s t).
Proof. exact (eq_refl (term217 A s t)). Qed.
Lemma lem6964915 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term274 A s t) = (term219 A s t).
Proof. exact (MK_COMB (@lem6964914 A s t) (@lem6964913 A s t)). Qed.
Lemma lem6964916 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6964917 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term279 A s t) = (term280 A s t).
Proof. exact (MK_COMB (@lem6964916) (@lem6964915 A s t)). Qed.
Lemma lem6964918 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term276 A s t x) = (term13 A s x t).
Proof. exact (eq_refl (term276 A s t x)). Qed.
Lemma lem6964919 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term217 A s t) = (term217 A s t).
Proof. exact (eq_refl (term217 A s t)). Qed.
Lemma lem6964920 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term281 A s t x) = (term282 A s x t).
Proof. exact (MK_COMB (@lem6964919 A s t) (@lem6964918 A s x t)). Qed.
Lemma lem6964921 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term283 A s t) = (term284 A s t).
Proof. exact (fun_ext (fun x : A => @lem6964920 A s x t)). Qed.
Lemma lem6964922 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6964923 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term275 A s t) = (term285 A s t).
Proof. exact (MK_COMB (@lem6964922 A) (@lem6964921 A s t)). Qed.
Lemma lem6964924 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term274 A s t) = (term275 A s t)) = ((term219 A s t) = (term285 A s t)).
Proof. exact (MK_COMB (@lem6964917 A s t) (@lem6964923 A s t)). Qed.
Lemma lem6964925 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term219 A s t) = (term285 A s t).
Proof. exact (EQ_MP (@lem6964924 A s t) (@lem6964909 A s t)). Qed.
Lemma lem6964926 {A : Type'} (s : A -> Prop) : (term234 A s) = (term286 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6964925 A s t)). Qed.
Lemma lem6964927 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964928 {A : Type'} (s : A -> Prop) : (term245 A s) = (term287 A s).
Proof. exact (MK_COMB (@lem6964927 A) (@lem6964926 A s)). Qed.
Lemma lem6964930 {A B : Type'} (P : type1413 A B) : (term288 A B P) = (term289 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6964931 {A : Type'} (P : type672 A) : (term290 A P) = (term291 A P).
Proof. exact (@lem6964930 (A -> Prop) A P). Qed.
Lemma lem6964932 {A : Type'} (s : A -> Prop) : (term292 A s) = (term293 A s).
Proof. exact (@lem6964931 A (term294 A s)). Qed.
Lemma lem6964933 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term295 A s t) = (term284 A s t).
Proof. exact (eq_refl (term295 A s t)). Qed.
Lemma lem6964934 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6964935 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term296 A s t x) = (term297 A s t x).
Proof. exact (MK_COMB (@lem6964933 A s t) (@lem6964934 A x)). Qed.
Lemma lem6964936 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term297 A s t x) = (term282 A s x t).
Proof. exact (eq_refl (term297 A s t x)). Qed.
Lemma lem6964937 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term296 A s t x) = (term282 A s x t).
Proof. exact (TRANS (@lem6964935 A s t x) (@lem6964936 A s x t)). Qed.
Lemma lem6964938 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term298 A s t) = (term284 A s t).
Proof. exact (fun_ext (fun x : A => @lem6964937 A s x t)). Qed.
Lemma lem6964939 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6964940 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term299 A s t) = (term285 A s t).
Proof. exact (MK_COMB (@lem6964939 A) (@lem6964938 A s t)). Qed.
Lemma lem6964941 {A : Type'} (s : A -> Prop) : (term300 A s) = (term286 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6964940 A s t)). Qed.
Lemma lem6964942 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964943 {A : Type'} (s : A -> Prop) : (term292 A s) = (term287 A s).
Proof. exact (MK_COMB (@lem6964942 A) (@lem6964941 A s)). Qed.
Lemma lem6964944 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6964945 {A : Type'} (s : A -> Prop) : (term301 A s) = (term302 A s).
Proof. exact (MK_COMB (@lem6964944) (@lem6964943 A s)). Qed.
Lemma lem6964946 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term295 A s t) = (term284 A s t).
Proof. exact (eq_refl (term295 A s t)). Qed.
Lemma lem6964947 {A : Type'} (x : type684 A) (t : A -> Prop) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem6964948 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term303 A s x t) = (term304 A s x t).
Proof. exact (MK_COMB (@lem6964946 A s t) (@lem6964947 A x t)). Qed.
Lemma lem6964949 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term304 A s x t) = (term305 A s x t).
Proof. exact (eq_refl (term304 A s x t)). Qed.
Lemma lem6964950 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term303 A s x t) = (term305 A s x t).
Proof. exact (TRANS (@lem6964948 A s x t) (@lem6964949 A s x t)). Qed.
Lemma lem6964951 {A : Type'} (s : A -> Prop) (x : type684 A) : (term306 A s x) = (term307 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6964950 A s x t)). Qed.
Lemma lem6964952 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964953 {A : Type'} (s : A -> Prop) (x : type684 A) : (term308 A s x) = (term309 A s x).
Proof. exact (MK_COMB (@lem6964952 A) (@lem6964951 A s x)). Qed.
Lemma lem6964954 {A : Type'} (s : A -> Prop) : (term310 A s) = (term311 A s).
Proof. exact (fun_ext (fun x : type684 A => @lem6964953 A s x)). Qed.
Lemma lem6964955 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem6964956 {A : Type'} (s : A -> Prop) : (term293 A s) = (term312 A s).
Proof. exact (MK_COMB (@lem6964955 A) (@lem6964954 A s)). Qed.
Lemma lem6964957 {A : Type'} (s : A -> Prop) : ((term292 A s) = (term293 A s)) = ((term287 A s) = (term312 A s)).
Proof. exact (MK_COMB (@lem6964945 A s) (@lem6964956 A s)). Qed.
Lemma lem6964958 {A : Type'} (s : A -> Prop) : (term287 A s) = (term312 A s).
Proof. exact (EQ_MP (@lem6964957 A s) (@lem6964932 A s)). Qed.
Lemma lem6964959 {A : Type'} (s : A -> Prop) : (term245 A s) = (term312 A s).
Proof. exact (TRANS (@lem6964928 A s) (@lem6964958 A s)). Qed.
Lemma lem6964960 {A : Type'} : (term256 A) = (term313 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6964959 A s)). Qed.
Lemma lem6964961 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964962 {A : Type'} : (term267 A) = (term314 A).
Proof. exact (MK_COMB (@lem6964961 A) (@lem6964960 A)). Qed.
Lemma lem6964964 {A B : Type'} (P : type1413 A B) : (term288 A B P) = (term289 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6964965 {A : Type'} (P : type597 A) : (term315 A P) = (term316 A P).
Proof. exact (@lem6964964 (A -> Prop) (type684 A) P). Qed.
Lemma lem6964966 {A : Type'} : (term317 A) = (term318 A).
Proof. exact (@lem6964965 A (term319 A)). Qed.
Lemma lem6964967 {A : Type'} (s : A -> Prop) : (term320 A s) = (term311 A s).
Proof. exact (eq_refl (term320 A s)). Qed.
Lemma lem6964968 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6964969 {A : Type'} (s : A -> Prop) (x : type684 A) : (term321 A s x) = (term322 A s x).
Proof. exact (MK_COMB (@lem6964967 A s) (@lem6964968 A x)). Qed.
Lemma lem6964970 {A : Type'} (s : A -> Prop) (x : type684 A) : (term322 A s x) = (term309 A s x).
Proof. exact (eq_refl (term322 A s x)). Qed.
Lemma lem6964971 {A : Type'} (s : A -> Prop) (x : type684 A) : (term321 A s x) = (term309 A s x).
Proof. exact (TRANS (@lem6964969 A s x) (@lem6964970 A s x)). Qed.
Lemma lem6964972 {A : Type'} (s : A -> Prop) : (term323 A s) = (term311 A s).
Proof. exact (fun_ext (fun x : type684 A => @lem6964971 A s x)). Qed.
Lemma lem6964973 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem6964974 {A : Type'} (s : A -> Prop) : (term324 A s) = (term312 A s).
Proof. exact (MK_COMB (@lem6964973 A) (@lem6964972 A s)). Qed.
Lemma lem6964975 {A : Type'} : (term325 A) = (term313 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6964974 A s)). Qed.
Lemma lem6964976 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964977 {A : Type'} : (term317 A) = (term314 A).
Proof. exact (MK_COMB (@lem6964976 A) (@lem6964975 A)). Qed.
Lemma lem6964978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6964979 {A : Type'} : (term326 A) = (term327 A).
Proof. exact (MK_COMB (@lem6964978) (@lem6964977 A)). Qed.
Lemma lem6964980 {A : Type'} (s : A -> Prop) : (term320 A s) = (term311 A s).
Proof. exact (eq_refl (term320 A s)). Qed.
Lemma lem6964981 {A : Type'} (x : type638 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem6964982 {A : Type'} (x : type638 A) (s : A -> Prop) : (term328 A x s) = (term329 A x s).
Proof. exact (MK_COMB (@lem6964980 A s) (@lem6964981 A x s)). Qed.
Lemma lem6964983 {A : Type'} (x : type638 A) (s : A -> Prop) : (term329 A x s) = (term330 A x s).
Proof. exact (eq_refl (term329 A x s)). Qed.
Lemma lem6964984 {A : Type'} (x : type638 A) (s : A -> Prop) : (term328 A x s) = (term330 A x s).
Proof. exact (TRANS (@lem6964982 A x s) (@lem6964983 A x s)). Qed.
Lemma lem6964985 {A : Type'} (x : type638 A) : (term331 A x) = (term332 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6964984 A x s)). Qed.
Lemma lem6964986 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6964987 {A : Type'} (x : type638 A) : (term333 A x) = (term334 A x).
Proof. exact (MK_COMB (@lem6964986 A) (@lem6964985 A x)). Qed.
Lemma lem6964988 {A : Type'} : (term335 A) = (term336 A).
Proof. exact (fun_ext (fun x : type638 A => @lem6964987 A x)). Qed.
Lemma lem6964989 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem6964990 {A : Type'} : (term318 A) = (term337 A).
Proof. exact (MK_COMB (@lem6964989 A) (@lem6964988 A)). Qed.
Lemma lem6964991 {A : Type'} : ((term317 A) = (term318 A)) = ((term314 A) = (term337 A)).
Proof. exact (MK_COMB (@lem6964979 A) (@lem6964990 A)). Qed.
Lemma lem6964992 {A : Type'} : (term314 A) = (term337 A).
Proof. exact (EQ_MP (@lem6964991 A) (@lem6964966 A)). Qed.
Lemma lem6964993 {A : Type'} : (term267 A) = (term337 A).
Proof. exact (TRANS (@lem6964962 A) (@lem6964992 A)). Qed.
Lemma lem6964994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6964995 {A : Type'} : (term269 A) = (term338 A).
Proof. exact (MK_COMB (@lem6964994) (@lem6964993 A)). Qed.
Lemma lem6964996 {A : Type'} : (term272 A) = (term272 A).
Proof. exact (eq_refl (term272 A)). Qed.
Lemma lem6964997 {A : Type'} : (term273 A) = (term339 A).
Proof. exact (MK_COMB (@lem6964995 A) (@lem6964996 A)). Qed.
Lemma lem6964999 {A : Type'} (P : A -> Prop) (Q : Prop) : (term340 A P Q) = (term341 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6965000 {A : Type'} (P : type139 A) (Q : Prop) : (term342 A P Q) = (term343 A P Q).
Proof. exact (@lem6964999 (type638 A) P Q). Qed.
Lemma lem6965001 {A : Type'} : (term344 A) = (term345 A).
Proof. exact (@lem6965000 A (term336 A) (term272 A)). Qed.
Lemma lem6965002 {A : Type'} (x : type638 A) : (term346 A x) = (term334 A x).
Proof. exact (eq_refl (term346 A x)). Qed.
Lemma lem6965003 {A : Type'} : (term347 A) = (term336 A).
Proof. exact (fun_ext (fun x : type638 A => @lem6965002 A x)). Qed.
Lemma lem6965004 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem6965005 {A : Type'} : (term348 A) = (term337 A).
Proof. exact (MK_COMB (@lem6965004 A) (@lem6965003 A)). Qed.
Lemma lem6965006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6965007 {A : Type'} : (term349 A) = (term338 A).
Proof. exact (MK_COMB (@lem6965006) (@lem6965005 A)). Qed.
Lemma lem6965008 {A : Type'} : (term272 A) = (term272 A).
Proof. exact (eq_refl (term272 A)). Qed.
Lemma lem6965009 {A : Type'} : (term344 A) = (term339 A).
Proof. exact (MK_COMB (@lem6965007 A) (@lem6965008 A)). Qed.
Lemma lem6965010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6965011 {A : Type'} : (term350 A) = (term351 A).
Proof. exact (MK_COMB (@lem6965010) (@lem6965009 A)). Qed.
Lemma lem6965012 {A : Type'} (x : type638 A) : (term346 A x) = (term334 A x).
Proof. exact (eq_refl (term346 A x)). Qed.
Lemma lem6965013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6965014 {A : Type'} (x : type638 A) : (term352 A x) = (term353 A x).
Proof. exact (MK_COMB (@lem6965013) (@lem6965012 A x)). Qed.
Lemma lem6965015 {A : Type'} : (term272 A) = (term272 A).
Proof. exact (eq_refl (term272 A)). Qed.
Lemma lem6965016 {A : Type'} (x : type638 A) : (term354 A x) = (term355 A x).
Proof. exact (MK_COMB (@lem6965014 A x) (@lem6965015 A)). Qed.
Lemma lem6965017 {A : Type'} : (term356 A) = (term357 A).
Proof. exact (fun_ext (fun x : type638 A => @lem6965016 A x)). Qed.
Lemma lem6965018 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem6965019 {A : Type'} : (term345 A) = (term358 A).
Proof. exact (MK_COMB (@lem6965018 A) (@lem6965017 A)). Qed.
Lemma lem6965020 {A : Type'} : ((term344 A) = (term345 A)) = ((term339 A) = (term358 A)).
Proof. exact (MK_COMB (@lem6965011 A) (@lem6965019 A)). Qed.
Lemma lem6965021 {A : Type'} : (term339 A) = (term358 A).
Proof. exact (EQ_MP (@lem6965020 A) (@lem6965001 A)). Qed.
Lemma lem6965022 {A : Type'} : (term273 A) = (term358 A).
Proof. exact (TRANS (@lem6964997 A) (@lem6965021 A)). Qed.
Lemma lem6965023 {A : Type'} : (term227 A) = (term358 A).
Proof. exact (TRANS (@lem6964905 A) (@lem6965022 A)). Qed.
Lemma lem6965024 {A : Type'} : (term106 A) = (term358 A).
Proof. exact (TRANS (@lem6964451 A) (@lem6965023 A)). Qed.
Lemma lem6965025 {A : Type'} (h1 : term106 A) : term358 A.
Proof. exact (EQ_MP (@lem6965024 A) (@lem6964227 A h1)). Qed.
Lemma lem6965033 {A : Type'} (x : A) (t : A -> Prop) : (term162 A x t) = (@IN A x t).
Proof. exact (@lem16933 (@IN A x t)). Qed.
Lemma lem6965035 {A : Type'} (x : A) (s : A -> Prop) : (term163 A x s) = (term163 A x s).
Proof. exact (eq_refl (term163 A x s)). Qed.
Lemma lem6965036 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term164 A s x t) = (term165 A s x t).
Proof. exact (MK_COMB (@lem6965035 A x s) (@lem6965033 A x t)). Qed.
Lemma lem6965037 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term166 A s x t) = (term164 A s x t).
Proof. exact (@lem17045 (@IN A x s) (term16 A x t)). Qed.
Lemma lem6965038 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term166 A s x t) = (term165 A s x t).
Proof. exact (TRANS (@lem6965037 A s x t) (@lem6965036 A s x t)). Qed.
Lemma lem6965044 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term359 A s x t) = (term359 A s x t).
Proof. exact (eq_refl (term359 A s x t)). Qed.
Lemma lem6965046 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term360 A x s t) = (term360 A x s t).
Proof. exact (eq_refl (term360 A x s t)). Qed.
Lemma lem6965047 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term361 A s x t) = (term362 A s x t).
Proof. exact (MK_COMB (@lem6965046 A x s t) (@lem6965038 A s x t)). Qed.
Lemma lem6965048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6965049 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term363 A s x t) = (term364 A s x t).
Proof. exact (MK_COMB (@lem6965048) (@lem6965047 A s x t)). Qed.
Lemma lem6965050 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term365 A s x t) = (term366 A s x t).
Proof. exact (MK_COMB (@lem6965049 A s x t) (@lem6965044 A s x t)). Qed.
Lemma lem6965051 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term12 A x s t) = (term13 A s x t)) = (term365 A s x t).
Proof. exact (@lem17784 (term12 A x s t) (term13 A s x t)). Qed.
Lemma lem6965052 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term12 A x s t) = (term13 A s x t)) = (term366 A s x t).
Proof. exact (TRANS (@lem6965051 A s x t) (@lem6965050 A s x t)). Qed.
Lemma lem6965053 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term144 A s t) = (term367 A s t).
Proof. exact (fun_ext (fun x : A => @lem6965052 A s x t)). Qed.
Lemma lem6965054 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6965055 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term145 A s t) = (term368 A s t).
Proof. exact (MK_COMB (@lem6965054 A) (@lem6965053 A s t)). Qed.
Lemma lem6965056 {A : Type'} (s : A -> Prop) : (term146 A s) = (term369 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6965055 A s t)). Qed.
Lemma lem6965057 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965058 {A : Type'} (s : A -> Prop) : (term147 A s) = (term370 A s).
Proof. exact (MK_COMB (@lem6965057 A) (@lem6965056 A s)). Qed.
Lemma lem6965059 {A : Type'} : (term148 A) = (term371 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6965058 A s)). Qed.
Lemma lem6965060 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965061 {A : Type'} : (term105 A) = (term372 A).
Proof. exact (MK_COMB (@lem6965060 A) (@lem6965059 A)). Qed.
Lemma lem6965071 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6965072 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (@lem6965071 A P Q). Qed.
Lemma lem6965073 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term373 A s t) = (term374 A s t).
Proof. exact (@lem6965072 A (term375 A s t) (term376 A s t)). Qed.
Lemma lem6965074 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term377 A s t x) = (term362 A s x t).
Proof. exact (eq_refl (term377 A s t x)). Qed.
Lemma lem6965075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6965076 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term378 A s t x) = (term364 A s x t).
Proof. exact (MK_COMB (@lem6965075) (@lem6965074 A s x t)). Qed.
Lemma lem6965077 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term379 A s t x) = (term359 A s x t).
Proof. exact (eq_refl (term379 A s t x)). Qed.
Lemma lem6965078 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term380 A s t x) = (term366 A s x t).
Proof. exact (MK_COMB (@lem6965076 A s x t) (@lem6965077 A s x t)). Qed.
Lemma lem6965079 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term381 A s t) = (term367 A s t).
Proof. exact (fun_ext (fun x : A => @lem6965078 A s x t)). Qed.
Lemma lem6965080 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6965081 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term373 A s t) = (term368 A s t).
Proof. exact (MK_COMB (@lem6965080 A) (@lem6965079 A s t)). Qed.
Lemma lem6965082 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6965083 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term382 A s t) = (term383 A s t).
Proof. exact (MK_COMB (@lem6965082) (@lem6965081 A s t)). Qed.
Lemma lem6965084 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term377 A s t x) = (term362 A s x t).
Proof. exact (eq_refl (term377 A s t x)). Qed.
Lemma lem6965085 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term384 A s t) = (term375 A s t).
Proof. exact (fun_ext (fun x : A => @lem6965084 A s x t)). Qed.
Lemma lem6965086 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6965087 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term385 A s t) = (term386 A s t).
Proof. exact (MK_COMB (@lem6965086 A) (@lem6965085 A s t)). Qed.
Lemma lem6965088 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6965089 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term387 A s t) = (term388 A s t).
Proof. exact (MK_COMB (@lem6965088) (@lem6965087 A s t)). Qed.
Lemma lem6965090 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term379 A s t x) = (term359 A s x t).
Proof. exact (eq_refl (term379 A s t x)). Qed.
Lemma lem6965091 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term389 A s t) = (term376 A s t).
Proof. exact (fun_ext (fun x : A => @lem6965090 A s x t)). Qed.
Lemma lem6965092 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6965093 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term390 A s t) = (term391 A s t).
Proof. exact (MK_COMB (@lem6965092 A) (@lem6965091 A s t)). Qed.
Lemma lem6965094 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term374 A s t) = (term392 A s t).
Proof. exact (MK_COMB (@lem6965089 A s t) (@lem6965093 A s t)). Qed.
Lemma lem6965095 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term373 A s t) = (term374 A s t)) = ((term368 A s t) = (term392 A s t)).
Proof. exact (MK_COMB (@lem6965083 A s t) (@lem6965094 A s t)). Qed.
Lemma lem6965096 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term368 A s t) = (term392 A s t).
Proof. exact (EQ_MP (@lem6965095 A s t) (@lem6965073 A s t)). Qed.
Lemma lem6965193 {A : Type'} (s : A -> Prop) : (term369 A s) = (term393 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6965096 A s t)). Qed.
Lemma lem6965194 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965195 {A : Type'} (s : A -> Prop) : (term370 A s) = (term394 A s).
Proof. exact (MK_COMB (@lem6965194 A) (@lem6965193 A s)). Qed.
Lemma lem6965197 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6965198 {A : Type'} (P : type686 A) (Q : type686 A) : (term230 A P Q) = (term231 A P Q).
Proof. exact (@lem6965197 (A -> Prop) P Q). Qed.
Lemma lem6965199 {A : Type'} (s : A -> Prop) : (term395 A s) = (term396 A s).
Proof. exact (@lem6965198 A (term397 A s) (term398 A s)). Qed.
Lemma lem6965200 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term399 A s t) = (term386 A s t).
Proof. exact (eq_refl (term399 A s t)). Qed.
Lemma lem6965201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6965202 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term400 A s t) = (term388 A s t).
Proof. exact (MK_COMB (@lem6965201) (@lem6965200 A s t)). Qed.
Lemma lem6965203 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term401 A s t) = (term391 A s t).
Proof. exact (eq_refl (term401 A s t)). Qed.
Lemma lem6965204 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term402 A s t) = (term392 A s t).
Proof. exact (MK_COMB (@lem6965202 A s t) (@lem6965203 A s t)). Qed.
Lemma lem6965205 {A : Type'} (s : A -> Prop) : (term403 A s) = (term393 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6965204 A s t)). Qed.
Lemma lem6965206 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965207 {A : Type'} (s : A -> Prop) : (term395 A s) = (term394 A s).
Proof. exact (MK_COMB (@lem6965206 A) (@lem6965205 A s)). Qed.
Lemma lem6965208 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6965209 {A : Type'} (s : A -> Prop) : (term404 A s) = (term405 A s).
Proof. exact (MK_COMB (@lem6965208) (@lem6965207 A s)). Qed.
Lemma lem6965210 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term399 A s t) = (term386 A s t).
Proof. exact (eq_refl (term399 A s t)). Qed.
Lemma lem6965211 {A : Type'} (s : A -> Prop) : (term406 A s) = (term397 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6965210 A s t)). Qed.
Lemma lem6965212 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965213 {A : Type'} (s : A -> Prop) : (term407 A s) = (term408 A s).
Proof. exact (MK_COMB (@lem6965212 A) (@lem6965211 A s)). Qed.
Lemma lem6965214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6965215 {A : Type'} (s : A -> Prop) : (term409 A s) = (term410 A s).
Proof. exact (MK_COMB (@lem6965214) (@lem6965213 A s)). Qed.
Lemma lem6965216 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term401 A s t) = (term391 A s t).
Proof. exact (eq_refl (term401 A s t)). Qed.
Lemma lem6965217 {A : Type'} (s : A -> Prop) : (term411 A s) = (term398 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6965216 A s t)). Qed.
Lemma lem6965218 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965219 {A : Type'} (s : A -> Prop) : (term412 A s) = (term413 A s).
Proof. exact (MK_COMB (@lem6965218 A) (@lem6965217 A s)). Qed.
Lemma lem6965220 {A : Type'} (s : A -> Prop) : (term396 A s) = (term414 A s).
Proof. exact (MK_COMB (@lem6965215 A s) (@lem6965219 A s)). Qed.
Lemma lem6965221 {A : Type'} (s : A -> Prop) : ((term395 A s) = (term396 A s)) = ((term394 A s) = (term414 A s)).
Proof. exact (MK_COMB (@lem6965209 A s) (@lem6965220 A s)). Qed.
Lemma lem6965222 {A : Type'} (s : A -> Prop) : (term394 A s) = (term414 A s).
Proof. exact (EQ_MP (@lem6965221 A s) (@lem6965199 A s)). Qed.
Lemma lem6965327 {A : Type'} (s : A -> Prop) : (term370 A s) = (term414 A s).
Proof. exact (TRANS (@lem6965195 A s) (@lem6965222 A s)). Qed.
Lemma lem6965328 {A : Type'} : (term371 A) = (term415 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6965327 A s)). Qed.
Lemma lem6965329 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965330 {A : Type'} : (term372 A) = (term416 A).
Proof. exact (MK_COMB (@lem6965329 A) (@lem6965328 A)). Qed.
Lemma lem6965332 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6965333 {A : Type'} (P : type686 A) (Q : type686 A) : (term230 A P Q) = (term231 A P Q).
Proof. exact (@lem6965332 (A -> Prop) P Q). Qed.
Lemma lem6965334 {A : Type'} : (term417 A) = (term418 A).
Proof. exact (@lem6965333 A (term419 A) (term420 A)). Qed.
Lemma lem6965335 {A : Type'} (s : A -> Prop) : (term421 A s) = (term408 A s).
Proof. exact (eq_refl (term421 A s)). Qed.
Lemma lem6965336 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6965337 {A : Type'} (s : A -> Prop) : (term422 A s) = (term410 A s).
Proof. exact (MK_COMB (@lem6965336) (@lem6965335 A s)). Qed.
Lemma lem6965338 {A : Type'} (s : A -> Prop) : (term423 A s) = (term413 A s).
Proof. exact (eq_refl (term423 A s)). Qed.
Lemma lem6965339 {A : Type'} (s : A -> Prop) : (term424 A s) = (term414 A s).
Proof. exact (MK_COMB (@lem6965337 A s) (@lem6965338 A s)). Qed.
Lemma lem6965340 {A : Type'} : (term425 A) = (term415 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6965339 A s)). Qed.
Lemma lem6965341 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965342 {A : Type'} : (term417 A) = (term416 A).
Proof. exact (MK_COMB (@lem6965341 A) (@lem6965340 A)). Qed.
Lemma lem6965343 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6965344 {A : Type'} : (term426 A) = (term427 A).
Proof. exact (MK_COMB (@lem6965343) (@lem6965342 A)). Qed.
Lemma lem6965345 {A : Type'} (s : A -> Prop) : (term421 A s) = (term408 A s).
Proof. exact (eq_refl (term421 A s)). Qed.
Lemma lem6965346 {A : Type'} : (term428 A) = (term419 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6965345 A s)). Qed.
Lemma lem6965347 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965348 {A : Type'} : (term429 A) = (term430 A).
Proof. exact (MK_COMB (@lem6965347 A) (@lem6965346 A)). Qed.
Lemma lem6965349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6965350 {A : Type'} : (term431 A) = (term432 A).
Proof. exact (MK_COMB (@lem6965349) (@lem6965348 A)). Qed.
Lemma lem6965351 {A : Type'} (s : A -> Prop) : (term423 A s) = (term413 A s).
Proof. exact (eq_refl (term423 A s)). Qed.
Lemma lem6965352 {A : Type'} : (term433 A) = (term420 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6965351 A s)). Qed.
Lemma lem6965353 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965354 {A : Type'} : (term434 A) = (term435 A).
Proof. exact (MK_COMB (@lem6965353 A) (@lem6965352 A)). Qed.
Lemma lem6965355 {A : Type'} : (term418 A) = (term436 A).
Proof. exact (MK_COMB (@lem6965350 A) (@lem6965354 A)). Qed.
Lemma lem6965356 {A : Type'} : ((term417 A) = (term418 A)) = ((term416 A) = (term436 A)).
Proof. exact (MK_COMB (@lem6965344 A) (@lem6965355 A)). Qed.
Lemma lem6965357 {A : Type'} : (term416 A) = (term436 A).
Proof. exact (EQ_MP (@lem6965356 A) (@lem6965334 A)). Qed.
Lemma lem6965472 {A : Type'} : (term372 A) = (term436 A).
Proof. exact (TRANS (@lem6965330 A) (@lem6965357 A)). Qed.
Lemma lem6965473 {A : Type'} : (term105 A) = (term436 A).
Proof. exact (TRANS (@lem6965061 A) (@lem6965472 A)). Qed.
Lemma lem6965474 {A : Type'} (h1 : term105 A) : term436 A.
Proof. exact (EQ_MP (@lem6965473 A) (@lem6964228 A h1)). Qed.
Lemma lem6965485 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term437 A s x t) = (term438 A s x t).
Proof. exact (@lem17160 (@IN A x s) (@IN A x t)). Qed.
Lemma lem6965491 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term439 A s x t) = (term439 A s x t).
Proof. exact (eq_refl (term439 A s x t)). Qed.
Lemma lem6965493 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term440 A x s t) = (term440 A x s t).
Proof. exact (eq_refl (term440 A x s t)). Qed.
Lemma lem6965494 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term441 A s x t) = (term442 A s x t).
Proof. exact (MK_COMB (@lem6965493 A x s t) (@lem6965485 A s x t)). Qed.
Lemma lem6965495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6965496 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term443 A s x t) = (term444 A s x t).
Proof. exact (MK_COMB (@lem6965495) (@lem6965494 A s x t)). Qed.
Lemma lem6965497 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term445 A s x t) = (term446 A s x t).
Proof. exact (MK_COMB (@lem6965496 A s x t) (@lem6965491 A s x t)). Qed.
Lemma lem6965498 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term3 A x s t) = (term4 A s x t)) = (term445 A s x t).
Proof. exact (@lem17784 (term3 A x s t) (term4 A s x t)). Qed.
Lemma lem6965499 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term3 A x s t) = (term4 A s x t)) = (term446 A s x t).
Proof. exact (TRANS (@lem6965498 A s x t) (@lem6965497 A s x t)). Qed.
Lemma lem6965500 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term139 A s t) = (term447 A s t).
Proof. exact (fun_ext (fun x : A => @lem6965499 A s x t)). Qed.
Lemma lem6965501 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6965502 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term140 A s t) = (term448 A s t).
Proof. exact (MK_COMB (@lem6965501 A) (@lem6965500 A s t)). Qed.
Lemma lem6965503 {A : Type'} (s : A -> Prop) : (term141 A s) = (term449 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6965502 A s t)). Qed.
Lemma lem6965504 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965505 {A : Type'} (s : A -> Prop) : (term142 A s) = (term450 A s).
Proof. exact (MK_COMB (@lem6965504 A) (@lem6965503 A s)). Qed.
Lemma lem6965506 {A : Type'} : (term143 A) = (term451 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6965505 A s)). Qed.
Lemma lem6965507 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965508 {A : Type'} : (term104 A) = (term452 A).
Proof. exact (MK_COMB (@lem6965507 A) (@lem6965506 A)). Qed.
Lemma lem6965518 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6965519 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (@lem6965518 A P Q). Qed.
Lemma lem6965520 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term453 A s t) = (term454 A s t).
Proof. exact (@lem6965519 A (term455 A s t) (term456 A s t)). Qed.
Lemma lem6965521 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term457 A s t x) = (term442 A s x t).
Proof. exact (eq_refl (term457 A s t x)). Qed.
Lemma lem6965522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6965523 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term458 A s t x) = (term444 A s x t).
Proof. exact (MK_COMB (@lem6965522) (@lem6965521 A s x t)). Qed.
Lemma lem6965524 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term459 A s t x) = (term439 A s x t).
Proof. exact (eq_refl (term459 A s t x)). Qed.
Lemma lem6965525 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term460 A s t x) = (term446 A s x t).
Proof. exact (MK_COMB (@lem6965523 A s x t) (@lem6965524 A s x t)). Qed.
Lemma lem6965526 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term461 A s t) = (term447 A s t).
Proof. exact (fun_ext (fun x : A => @lem6965525 A s x t)). Qed.
Lemma lem6965527 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6965528 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term453 A s t) = (term448 A s t).
Proof. exact (MK_COMB (@lem6965527 A) (@lem6965526 A s t)). Qed.
Lemma lem6965529 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6965530 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term462 A s t) = (term463 A s t).
Proof. exact (MK_COMB (@lem6965529) (@lem6965528 A s t)). Qed.
Lemma lem6965531 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term457 A s t x) = (term442 A s x t).
Proof. exact (eq_refl (term457 A s t x)). Qed.
Lemma lem6965532 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term464 A s t) = (term455 A s t).
Proof. exact (fun_ext (fun x : A => @lem6965531 A s x t)). Qed.
Lemma lem6965533 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6965534 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term465 A s t) = (term466 A s t).
Proof. exact (MK_COMB (@lem6965533 A) (@lem6965532 A s t)). Qed.
Lemma lem6965535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6965536 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term467 A s t) = (term468 A s t).
Proof. exact (MK_COMB (@lem6965535) (@lem6965534 A s t)). Qed.
Lemma lem6965537 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term459 A s t x) = (term439 A s x t).
Proof. exact (eq_refl (term459 A s t x)). Qed.
Lemma lem6965538 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term469 A s t) = (term456 A s t).
Proof. exact (fun_ext (fun x : A => @lem6965537 A s x t)). Qed.
Lemma lem6965539 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6965540 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term470 A s t) = (term471 A s t).
Proof. exact (MK_COMB (@lem6965539 A) (@lem6965538 A s t)). Qed.
Lemma lem6965541 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term454 A s t) = (term472 A s t).
Proof. exact (MK_COMB (@lem6965536 A s t) (@lem6965540 A s t)). Qed.
Lemma lem6965542 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term453 A s t) = (term454 A s t)) = ((term448 A s t) = (term472 A s t)).
Proof. exact (MK_COMB (@lem6965530 A s t) (@lem6965541 A s t)). Qed.
Lemma lem6965543 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term448 A s t) = (term472 A s t).
Proof. exact (EQ_MP (@lem6965542 A s t) (@lem6965520 A s t)). Qed.
Lemma lem6965640 {A : Type'} (s : A -> Prop) : (term449 A s) = (term473 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6965543 A s t)). Qed.
Lemma lem6965641 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965642 {A : Type'} (s : A -> Prop) : (term450 A s) = (term474 A s).
Proof. exact (MK_COMB (@lem6965641 A) (@lem6965640 A s)). Qed.
Lemma lem6965644 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6965645 {A : Type'} (P : type686 A) (Q : type686 A) : (term230 A P Q) = (term231 A P Q).
Proof. exact (@lem6965644 (A -> Prop) P Q). Qed.
Lemma lem6965646 {A : Type'} (s : A -> Prop) : (term475 A s) = (term476 A s).
Proof. exact (@lem6965645 A (term477 A s) (term478 A s)). Qed.
Lemma lem6965647 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term479 A s t) = (term466 A s t).
Proof. exact (eq_refl (term479 A s t)). Qed.
Lemma lem6965648 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6965649 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term480 A s t) = (term468 A s t).
Proof. exact (MK_COMB (@lem6965648) (@lem6965647 A s t)). Qed.
Lemma lem6965650 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term481 A s t) = (term471 A s t).
Proof. exact (eq_refl (term481 A s t)). Qed.
Lemma lem6965651 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term482 A s t) = (term472 A s t).
Proof. exact (MK_COMB (@lem6965649 A s t) (@lem6965650 A s t)). Qed.
Lemma lem6965652 {A : Type'} (s : A -> Prop) : (term483 A s) = (term473 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6965651 A s t)). Qed.
Lemma lem6965653 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965654 {A : Type'} (s : A -> Prop) : (term475 A s) = (term474 A s).
Proof. exact (MK_COMB (@lem6965653 A) (@lem6965652 A s)). Qed.
Lemma lem6965655 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6965656 {A : Type'} (s : A -> Prop) : (term484 A s) = (term485 A s).
Proof. exact (MK_COMB (@lem6965655) (@lem6965654 A s)). Qed.
Lemma lem6965657 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term479 A s t) = (term466 A s t).
Proof. exact (eq_refl (term479 A s t)). Qed.
Lemma lem6965658 {A : Type'} (s : A -> Prop) : (term486 A s) = (term477 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6965657 A s t)). Qed.
Lemma lem6965659 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965660 {A : Type'} (s : A -> Prop) : (term487 A s) = (term488 A s).
Proof. exact (MK_COMB (@lem6965659 A) (@lem6965658 A s)). Qed.
Lemma lem6965661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6965662 {A : Type'} (s : A -> Prop) : (term489 A s) = (term490 A s).
Proof. exact (MK_COMB (@lem6965661) (@lem6965660 A s)). Qed.
Lemma lem6965663 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term481 A s t) = (term471 A s t).
Proof. exact (eq_refl (term481 A s t)). Qed.
Lemma lem6965664 {A : Type'} (s : A -> Prop) : (term491 A s) = (term478 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6965663 A s t)). Qed.
Lemma lem6965665 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965666 {A : Type'} (s : A -> Prop) : (term492 A s) = (term493 A s).
Proof. exact (MK_COMB (@lem6965665 A) (@lem6965664 A s)). Qed.
Lemma lem6965667 {A : Type'} (s : A -> Prop) : (term476 A s) = (term494 A s).
Proof. exact (MK_COMB (@lem6965662 A s) (@lem6965666 A s)). Qed.
Lemma lem6965668 {A : Type'} (s : A -> Prop) : ((term475 A s) = (term476 A s)) = ((term474 A s) = (term494 A s)).
Proof. exact (MK_COMB (@lem6965656 A s) (@lem6965667 A s)). Qed.
Lemma lem6965669 {A : Type'} (s : A -> Prop) : (term474 A s) = (term494 A s).
Proof. exact (EQ_MP (@lem6965668 A s) (@lem6965646 A s)). Qed.
Lemma lem6965774 {A : Type'} (s : A -> Prop) : (term450 A s) = (term494 A s).
Proof. exact (TRANS (@lem6965642 A s) (@lem6965669 A s)). Qed.
Lemma lem6965775 {A : Type'} : (term451 A) = (term495 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6965774 A s)). Qed.
Lemma lem6965776 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965777 {A : Type'} : (term452 A) = (term496 A).
Proof. exact (MK_COMB (@lem6965776 A) (@lem6965775 A)). Qed.
Lemma lem6965779 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6965780 {A : Type'} (P : type686 A) (Q : type686 A) : (term230 A P Q) = (term231 A P Q).
Proof. exact (@lem6965779 (A -> Prop) P Q). Qed.
Lemma lem6965781 {A : Type'} : (term497 A) = (term498 A).
Proof. exact (@lem6965780 A (term499 A) (term500 A)). Qed.
Lemma lem6965782 {A : Type'} (s : A -> Prop) : (term501 A s) = (term488 A s).
Proof. exact (eq_refl (term501 A s)). Qed.
Lemma lem6965783 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6965784 {A : Type'} (s : A -> Prop) : (term502 A s) = (term490 A s).
Proof. exact (MK_COMB (@lem6965783) (@lem6965782 A s)). Qed.
Lemma lem6965785 {A : Type'} (s : A -> Prop) : (term503 A s) = (term493 A s).
Proof. exact (eq_refl (term503 A s)). Qed.
Lemma lem6965786 {A : Type'} (s : A -> Prop) : (term504 A s) = (term494 A s).
Proof. exact (MK_COMB (@lem6965784 A s) (@lem6965785 A s)). Qed.
Lemma lem6965787 {A : Type'} : (term505 A) = (term495 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6965786 A s)). Qed.
Lemma lem6965788 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965789 {A : Type'} : (term497 A) = (term496 A).
Proof. exact (MK_COMB (@lem6965788 A) (@lem6965787 A)). Qed.
Lemma lem6965790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6965791 {A : Type'} : (term506 A) = (term507 A).
Proof. exact (MK_COMB (@lem6965790) (@lem6965789 A)). Qed.
Lemma lem6965792 {A : Type'} (s : A -> Prop) : (term501 A s) = (term488 A s).
Proof. exact (eq_refl (term501 A s)). Qed.
Lemma lem6965793 {A : Type'} : (term508 A) = (term499 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6965792 A s)). Qed.
Lemma lem6965794 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965795 {A : Type'} : (term509 A) = (term510 A).
Proof. exact (MK_COMB (@lem6965794 A) (@lem6965793 A)). Qed.
Lemma lem6965796 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6965797 {A : Type'} : (term511 A) = (term512 A).
Proof. exact (MK_COMB (@lem6965796) (@lem6965795 A)). Qed.
Lemma lem6965798 {A : Type'} (s : A -> Prop) : (term503 A s) = (term493 A s).
Proof. exact (eq_refl (term503 A s)). Qed.
Lemma lem6965799 {A : Type'} : (term513 A) = (term500 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6965798 A s)). Qed.
Lemma lem6965800 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965801 {A : Type'} : (term514 A) = (term515 A).
Proof. exact (MK_COMB (@lem6965800 A) (@lem6965799 A)). Qed.
Lemma lem6965802 {A : Type'} : (term498 A) = (term516 A).
Proof. exact (MK_COMB (@lem6965797 A) (@lem6965801 A)). Qed.
Lemma lem6965803 {A : Type'} : ((term497 A) = (term498 A)) = ((term496 A) = (term516 A)).
Proof. exact (MK_COMB (@lem6965791 A) (@lem6965802 A)). Qed.
Lemma lem6965804 {A : Type'} : (term496 A) = (term516 A).
Proof. exact (EQ_MP (@lem6965803 A) (@lem6965781 A)). Qed.
Lemma lem6965919 {A : Type'} : (term452 A) = (term516 A).
Proof. exact (TRANS (@lem6965777 A) (@lem6965804 A)). Qed.
Lemma lem6965920 {A : Type'} : (term104 A) = (term516 A).
Proof. exact (TRANS (@lem6965508 A) (@lem6965919 A)). Qed.
Lemma lem6965921 {A : Type'} (h1 : term104 A) : term516 A.
Proof. exact (EQ_MP (@lem6965920 A) (@lem6964229 A h1)). Qed.
Lemma lem6965922 {A : Type'} (x : type638 A) (h1 : term355 A x) : term355 A x.
Proof. exact (h1). Qed.
Lemma lem6965954 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term170 A v u f x) = (term170 A v u f x).
Proof. exact (eq_refl (term170 A v u f x)). Qed.
Lemma lem6965955 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term171 A v u f) = (term171 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6965954 A v u f x)). Qed.
Lemma lem6965956 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6965957 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term172 A v u f) = (term172 A v u f).
Proof. exact (MK_COMB (@lem6965956 A) (@lem6965955 A v u f)). Qed.
Lemma lem6965958 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) : term172 A v u f.
Proof. exact (EQ_MP (@lem6965957 A v u f) (@lem6964306 A v u f h1)). Qed.
Lemma lem6965987 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term359 A s x t) = (term359 A s x t).
Proof. exact (eq_refl (term359 A s x t)). Qed.
Lemma lem6965988 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term376 A s t) = (term376 A s t).
Proof. exact (fun_ext (fun x : A => @lem6965987 A s x t)). Qed.
Lemma lem6965989 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6965990 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term391 A s t) = (term391 A s t).
Proof. exact (MK_COMB (@lem6965989 A) (@lem6965988 A s t)). Qed.
Lemma lem6965991 {A : Type'} (s : A -> Prop) : (term398 A s) = (term398 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6965990 A s t)). Qed.
Lemma lem6965992 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965993 {A : Type'} (s : A -> Prop) : (term413 A s) = (term413 A s).
Proof. exact (MK_COMB (@lem6965992 A) (@lem6965991 A s)). Qed.
Lemma lem6965994 {A : Type'} : (term420 A) = (term420 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6965993 A s)). Qed.
Lemma lem6965995 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6965996 {A : Type'} : (term435 A) = (term435 A).
Proof. exact (MK_COMB (@lem6965995 A) (@lem6965994 A)). Qed.
Lemma lem6966023 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term362 A s x t) = (term362 A s x t).
Proof. exact (eq_refl (term362 A s x t)). Qed.
Lemma lem6966024 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term375 A s t) = (term375 A s t).
Proof. exact (fun_ext (fun x : A => @lem6966023 A s x t)). Qed.
Lemma lem6966025 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6966026 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term386 A s t) = (term386 A s t).
Proof. exact (MK_COMB (@lem6966025 A) (@lem6966024 A s t)). Qed.
Lemma lem6966027 {A : Type'} (s : A -> Prop) : (term397 A s) = (term397 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6966026 A s t)). Qed.
Lemma lem6966028 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966029 {A : Type'} (s : A -> Prop) : (term408 A s) = (term408 A s).
Proof. exact (MK_COMB (@lem6966028 A) (@lem6966027 A s)). Qed.
Lemma lem6966030 {A : Type'} : (term419 A) = (term419 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6966029 A s)). Qed.
Lemma lem6966031 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966032 {A : Type'} : (term430 A) = (term430 A).
Proof. exact (MK_COMB (@lem6966031 A) (@lem6966030 A)). Qed.
Lemma lem6966033 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6966034 {A : Type'} : (term432 A) = (term432 A).
Proof. exact (MK_COMB (@lem6966033) (@lem6966032 A)). Qed.
Lemma lem6966035 {A : Type'} : (term436 A) = (term436 A).
Proof. exact (MK_COMB (@lem6966034 A) (@lem6965996 A)). Qed.
Lemma lem6966036 {A : Type'} (h1 : term105 A) : term436 A.
Proof. exact (EQ_MP (@lem6966035 A) (@lem6965474 A h1)). Qed.
Lemma lem6966063 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term439 A s x t) = (term439 A s x t).
Proof. exact (eq_refl (term439 A s x t)). Qed.
Lemma lem6966064 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term456 A s t) = (term456 A s t).
Proof. exact (fun_ext (fun x : A => @lem6966063 A s x t)). Qed.
Lemma lem6966065 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6966066 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term471 A s t) = (term471 A s t).
Proof. exact (MK_COMB (@lem6966065 A) (@lem6966064 A s t)). Qed.
Lemma lem6966067 {A : Type'} (s : A -> Prop) : (term478 A s) = (term478 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6966066 A s t)). Qed.
Lemma lem6966068 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966069 {A : Type'} (s : A -> Prop) : (term493 A s) = (term493 A s).
Proof. exact (MK_COMB (@lem6966068 A) (@lem6966067 A s)). Qed.
Lemma lem6966070 {A : Type'} : (term500 A) = (term500 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6966069 A s)). Qed.
Lemma lem6966071 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966072 {A : Type'} : (term515 A) = (term515 A).
Proof. exact (MK_COMB (@lem6966071 A) (@lem6966070 A)). Qed.
Lemma lem6966101 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term442 A s x t) = (term442 A s x t).
Proof. exact (eq_refl (term442 A s x t)). Qed.
Lemma lem6966102 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term455 A s t) = (term455 A s t).
Proof. exact (fun_ext (fun x : A => @lem6966101 A s x t)). Qed.
Lemma lem6966103 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6966104 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term466 A s t) = (term466 A s t).
Proof. exact (MK_COMB (@lem6966103 A) (@lem6966102 A s t)). Qed.
Lemma lem6966105 {A : Type'} (s : A -> Prop) : (term477 A s) = (term477 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6966104 A s t)). Qed.
Lemma lem6966106 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966107 {A : Type'} (s : A -> Prop) : (term488 A s) = (term488 A s).
Proof. exact (MK_COMB (@lem6966106 A) (@lem6966105 A s)). Qed.
Lemma lem6966108 {A : Type'} : (term499 A) = (term499 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6966107 A s)). Qed.
Lemma lem6966109 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966110 {A : Type'} : (term510 A) = (term510 A).
Proof. exact (MK_COMB (@lem6966109 A) (@lem6966108 A)). Qed.
Lemma lem6966111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6966112 {A : Type'} : (term512 A) = (term512 A).
Proof. exact (MK_COMB (@lem6966111) (@lem6966110 A)). Qed.
Lemma lem6966113 {A : Type'} : (term516 A) = (term516 A).
Proof. exact (MK_COMB (@lem6966112 A) (@lem6966072 A)). Qed.
Lemma lem6966114 {A : Type'} (h1 : term104 A) : term516 A.
Proof. exact (EQ_MP (@lem6966113 A) (@lem6965921 A h1)). Qed.
Lemma lem6966129 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term165 A s x t) = (term165 A s x t).
Proof. exact (eq_refl (term165 A s x t)). Qed.
Lemma lem6966130 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term212 A s t) = (term212 A s t).
Proof. exact (fun_ext (fun x : A => @lem6966129 A s x t)). Qed.
Lemma lem6966131 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6966132 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term213 A s t) = (term213 A s t).
Proof. exact (MK_COMB (@lem6966131 A) (@lem6966130 A s t)). Qed.
Lemma lem6966141 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term214 A s t) = (term214 A s t).
Proof. exact (eq_refl (term214 A s t)). Qed.
Lemma lem6966142 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term216 A s t) = (term216 A s t).
Proof. exact (MK_COMB (@lem6966141 A s t) (@lem6966132 A s t)). Qed.
Lemma lem6966143 {A : Type'} (s : A -> Prop) : (term235 A s) = (term235 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6966142 A s t)). Qed.
Lemma lem6966144 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966145 {A : Type'} (s : A -> Prop) : (term250 A s) = (term250 A s).
Proof. exact (MK_COMB (@lem6966144 A) (@lem6966143 A s)). Qed.
Lemma lem6966146 {A : Type'} : (term257 A) = (term257 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6966145 A s)). Qed.
Lemma lem6966147 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966148 {A : Type'} : (term272 A) = (term272 A).
Proof. exact (MK_COMB (@lem6966147 A) (@lem6966146 A)). Qed.
Lemma lem6966179 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term517 A x s t) = (term517 A x s t).
Proof. exact (eq_refl (term517 A x s t)). Qed.
Lemma lem6966180 {A : Type'} (x : type638 A) (s : A -> Prop) : (term518 A x s) = (term518 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6966179 A x s t)). Qed.
Lemma lem6966181 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966182 {A : Type'} (x : type638 A) (s : A -> Prop) : (term330 A x s) = (term330 A x s).
Proof. exact (MK_COMB (@lem6966181 A) (@lem6966180 A x s)). Qed.
Lemma lem6966183 {A : Type'} (x : type638 A) : (term332 A x) = (term332 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6966182 A x s)). Qed.
Lemma lem6966184 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966185 {A : Type'} (x : type638 A) : (term334 A x) = (term334 A x).
Proof. exact (MK_COMB (@lem6966184 A) (@lem6966183 A x)). Qed.
Lemma lem6966186 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6966187 {A : Type'} (x : type638 A) : (term353 A x) = (term353 A x).
Proof. exact (MK_COMB (@lem6966186) (@lem6966185 A x)). Qed.
Lemma lem6966188 {A : Type'} (x : type638 A) : (term355 A x) = (term355 A x).
Proof. exact (MK_COMB (@lem6966187 A x) (@lem6966148 A)). Qed.
Lemma lem6966189 {A : Type'} (x : type638 A) (h1 : term355 A x) : term355 A x.
Proof. exact (EQ_MP (@lem6966188 A x) (@lem6965922 A x h1)). Qed.
Lemma lem6966245 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term200 A v u f x') : term200 A v u f x'.
Proof. exact (h1). Qed.
Lemma lem6966247 {A : Type'} (x : type638 A) (h1 : term355 A x) : term334 A x.
Proof. exact (proj1 (@lem6966189 A x h1)). Qed.
Lemma lem6966248 {A : Type'} (h1 : term104 A) : term515 A.
Proof. exact (proj2 (@lem6966114 A h1)). Qed.
Lemma lem6966249 {A : Type'} (h1 : term104 A) : term510 A.
Proof. exact (proj1 (@lem6966114 A h1)). Qed.
Lemma lem6966250 {A : Type'} (h1 : term105 A) : term435 A.
Proof. exact (proj2 (@lem6966036 A h1)). Qed.
Lemma lem6966253 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term174 A v u f x') : term174 A v u f x'.
Proof. exact (h1). Qed.
Lemma lem6966255 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term174 A v u f x') : term175 A v x' u.
Proof. exact (proj1 (@lem6966253 A v u f x' h1)). Qed.
Lemma lem6966298 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term517 A x s t) = (term519 A x s t).
Proof. exact (@lem19490 (term520 A x t s) (@SUBSET A s t) (term521 A x s t)). Qed.
Lemma lem6966299 {A : Type'} (x : type638 A) (s : A -> Prop) : (term518 A x s) = (term522 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6966298 A x s t)). Qed.
Lemma lem6966300 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966301 {A : Type'} (x : type638 A) (s : A -> Prop) : (term330 A x s) = (term523 A x s).
Proof. exact (MK_COMB (@lem6966300 A) (@lem6966299 A x s)). Qed.
Lemma lem6966302 {A : Type'} (x : type638 A) : (term332 A x) = (term524 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6966301 A x s)). Qed.
Lemma lem6966303 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966305 {A : Type'} (x : type638 A) : (term334 A x) = (term525 A x).
Proof. exact (MK_COMB (@lem6966303 A) (@lem6966302 A x)). Qed.
Lemma lem6966306 {A : Type'} (x : type638 A) (h1 : term355 A x) : term525 A x.
Proof. exact (EQ_MP (@lem6966305 A x) (@lem6966247 A x h1)). Qed.
Lemma lem6966374 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term442 A s x t) = (term526 A s x t).
Proof. exact (@lem19490 (term16 A x s) (term3 A x s t) (term16 A x t)). Qed.
Lemma lem6966375 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term455 A s t) = (term527 A s t).
Proof. exact (fun_ext (fun x : A => @lem6966374 A s x t)). Qed.
Lemma lem6966376 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6966377 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term466 A s t) = (term528 A s t).
Proof. exact (MK_COMB (@lem6966376 A) (@lem6966375 A s t)). Qed.
Lemma lem6966378 {A : Type'} (s : A -> Prop) : (term477 A s) = (term529 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6966377 A s t)). Qed.
Lemma lem6966379 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966380 {A : Type'} (s : A -> Prop) : (term488 A s) = (term530 A s).
Proof. exact (MK_COMB (@lem6966379 A) (@lem6966378 A s)). Qed.
Lemma lem6966381 {A : Type'} : (term499 A) = (term531 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6966380 A s)). Qed.
Lemma lem6966382 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966384 {A : Type'} : (term510 A) = (term532 A).
Proof. exact (MK_COMB (@lem6966382 A) (@lem6966381 A)). Qed.
Lemma lem6966385 {A : Type'} (h1 : term104 A) : term532 A.
Proof. exact (EQ_MP (@lem6966384 A) (@lem6966249 A h1)). Qed.
Lemma lem6966468 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term193 A v u) : term193 A v u.
Proof. exact (h1). Qed.
Lemma lem6966486 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term170 A v u f x) = (term170 A v u f x).
Proof. exact (eq_refl (term170 A v u f x)). Qed.
Lemma lem6966487 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term171 A v u f) = (term171 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6966486 A v u f x)). Qed.
Lemma lem6966488 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6966490 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term172 A v u f) = (term172 A v u f).
Proof. exact (MK_COMB (@lem6966488 A) (@lem6966487 A v u f)). Qed.
Lemma lem6966491 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) : term172 A v u f.
Proof. exact (EQ_MP (@lem6966490 A v u f) (@lem6965958 A v u f h1)). Qed.
Lemma lem6966610 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term439 A s x t) = (term439 A s x t).
Proof. exact (eq_refl (term439 A s x t)). Qed.
Lemma lem6966611 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term456 A s t) = (term456 A s t).
Proof. exact (fun_ext (fun x : A => @lem6966610 A s x t)). Qed.
Lemma lem6966612 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6966613 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term471 A s t) = (term471 A s t).
Proof. exact (MK_COMB (@lem6966612 A) (@lem6966611 A s t)). Qed.
Lemma lem6966614 {A : Type'} (s : A -> Prop) : (term478 A s) = (term478 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6966613 A s t)). Qed.
Lemma lem6966615 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966616 {A : Type'} (s : A -> Prop) : (term493 A s) = (term493 A s).
Proof. exact (MK_COMB (@lem6966615 A) (@lem6966614 A s)). Qed.
Lemma lem6966617 {A : Type'} : (term500 A) = (term500 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6966616 A s)). Qed.
Lemma lem6966618 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966620 {A : Type'} : (term515 A) = (term515 A).
Proof. exact (MK_COMB (@lem6966618 A) (@lem6966617 A)). Qed.
Lemma lem6966621 {A : Type'} (h1 : term104 A) : term515 A.
Proof. exact (EQ_MP (@lem6966620 A) (@lem6966248 A h1)). Qed.
Lemma lem6966664 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term359 A s x t) = (term533 A s x t).
Proof. exact (@lem19490 (@IN A x s) (term534 A x s t) (term16 A x t)). Qed.
Lemma lem6966665 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term376 A s t) = (term535 A s t).
Proof. exact (fun_ext (fun x : A => @lem6966664 A s x t)). Qed.
Lemma lem6966666 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6966667 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term391 A s t) = (term536 A s t).
Proof. exact (MK_COMB (@lem6966666 A) (@lem6966665 A s t)). Qed.
Lemma lem6966668 {A : Type'} (s : A -> Prop) : (term398 A s) = (term537 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6966667 A s t)). Qed.
Lemma lem6966669 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966670 {A : Type'} (s : A -> Prop) : (term413 A s) = (term538 A s).
Proof. exact (MK_COMB (@lem6966669 A) (@lem6966668 A s)). Qed.
Lemma lem6966671 {A : Type'} : (term420 A) = (term539 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6966670 A s)). Qed.
Lemma lem6966672 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6966674 {A : Type'} : (term435 A) = (term540 A).
Proof. exact (MK_COMB (@lem6966672 A) (@lem6966671 A)). Qed.
Lemma lem6966675 {A : Type'} (h1 : term105 A) : term540 A.
Proof. exact (EQ_MP (@lem6966674 A) (@lem6966250 A h1)). Qed.
Lemma lem6966691 {A : Type'} (_92737 : A -> Prop) (x : type638 A) (h1 : term355 A x) : term541 A x _92737.
Proof. exact (@lem6966306 A x h1 _92737). Qed.
Lemma lem6966692 {A : Type'} (x : type638 A) (_92737 : A -> Prop) : (term541 A x _92737) = (term523 A x _92737).
Proof. exact (eq_refl (term541 A x _92737)). Qed.
Lemma lem6966693 {A : Type'} (_92737 : A -> Prop) (x : type638 A) (h1 : term355 A x) : term523 A x _92737.
Proof. exact (EQ_MP (@lem6966692 A x _92737) (@lem6966691 A _92737 x h1)). Qed.
Lemma lem6966694 {A : Type'} (_92737 : A -> Prop) (_92738 : A -> Prop) (x : type638 A) (h1 : term355 A x) : term542 A x _92737 _92738.
Proof. exact (@lem6966693 A _92737 x h1 _92738). Qed.
Lemma lem6966695 {A : Type'} (x : type638 A) (_92737 : A -> Prop) (_92738 : A -> Prop) : (term542 A x _92737 _92738) = (term519 A x _92737 _92738).
Proof. exact (eq_refl (term542 A x _92737 _92738)). Qed.
Lemma lem6966696 {A : Type'} (_92737 : A -> Prop) (_92738 : A -> Prop) (x : type638 A) (h1 : term355 A x) : term519 A x _92737 _92738.
Proof. exact (EQ_MP (@lem6966695 A x _92737 _92738) (@lem6966694 A _92737 _92738 x h1)). Qed.
Lemma lem6966706 {A : Type'} (_92742 : A -> Prop) (h1 : term104 A) : term543 A _92742.
Proof. exact (@lem6966385 A h1 _92742). Qed.
Lemma lem6966707 {A : Type'} (_92742 : A -> Prop) : (term543 A _92742) = (term530 A _92742).
Proof. exact (eq_refl (term543 A _92742)). Qed.
Lemma lem6966708 {A : Type'} (_92742 : A -> Prop) (h1 : term104 A) : term530 A _92742.
Proof. exact (EQ_MP (@lem6966707 A _92742) (@lem6966706 A _92742 h1)). Qed.
Lemma lem6966709 {A : Type'} (_92742 : A -> Prop) (_92743 : A -> Prop) (h1 : term104 A) : term544 A _92742 _92743.
Proof. exact (@lem6966708 A _92742 h1 _92743). Qed.
Lemma lem6966710 {A : Type'} (_92742 : A -> Prop) (_92743 : A -> Prop) : (term544 A _92742 _92743) = (term528 A _92742 _92743).
Proof. exact (eq_refl (term544 A _92742 _92743)). Qed.
Lemma lem6966711 {A : Type'} (_92742 : A -> Prop) (_92743 : A -> Prop) (h1 : term104 A) : term528 A _92742 _92743.
Proof. exact (EQ_MP (@lem6966710 A _92742 _92743) (@lem6966709 A _92742 _92743 h1)). Qed.
Lemma lem6966712 {A : Type'} (_92742 : A -> Prop) (_92743 : A -> Prop) (_92744 : A) (h1 : term104 A) : term545 A _92742 _92743 _92744.
Proof. exact (@lem6966711 A _92742 _92743 h1 _92744). Qed.
Lemma lem6966713 {A : Type'} (_92742 : A -> Prop) (_92744 : A) (_92743 : A -> Prop) : (term545 A _92742 _92743 _92744) = (term526 A _92742 _92744 _92743).
Proof. exact (eq_refl (term545 A _92742 _92743 _92744)). Qed.
Lemma lem6966714 {A : Type'} (_92742 : A -> Prop) (_92744 : A) (_92743 : A -> Prop) (h1 : term104 A) : term526 A _92742 _92744 _92743.
Proof. exact (EQ_MP (@lem6966713 A _92742 _92744 _92743) (@lem6966712 A _92742 _92743 _92744 h1)). Qed.
Lemma lem6966742 {A : Type'} (_92754 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) : term546 A v u f _92754.
Proof. exact (@lem6966491 A v u f h1 _92754). Qed.
Lemma lem6966743 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (_92754 : A) : (term546 A v u f _92754) = (term170 A v u f _92754).
Proof. exact (eq_refl (term546 A v u f _92754)). Qed.
Lemma lem6966744 {A : Type'} (_92754 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) : term170 A v u f _92754.
Proof. exact (EQ_MP (@lem6966743 A v u f _92754) (@lem6966742 A _92754 v u f h1)). Qed.
Lemma lem6966769 {A : Type'} (_92763 : A -> Prop) (h1 : term104 A) : term503 A _92763.
Proof. exact (@lem6966621 A h1 _92763). Qed.
Lemma lem6966770 {A : Type'} (_92763 : A -> Prop) : (term503 A _92763) = (term493 A _92763).
Proof. exact (eq_refl (term503 A _92763)). Qed.
Lemma lem6966771 {A : Type'} (_92763 : A -> Prop) (h1 : term104 A) : term493 A _92763.
Proof. exact (EQ_MP (@lem6966770 A _92763) (@lem6966769 A _92763 h1)). Qed.
Lemma lem6966772 {A : Type'} (_92763 : A -> Prop) (_92764 : A -> Prop) (h1 : term104 A) : term481 A _92763 _92764.
Proof. exact (@lem6966771 A _92763 h1 _92764). Qed.
Lemma lem6966773 {A : Type'} (_92763 : A -> Prop) (_92764 : A -> Prop) : (term481 A _92763 _92764) = (term471 A _92763 _92764).
Proof. exact (eq_refl (term481 A _92763 _92764)). Qed.
Lemma lem6966774 {A : Type'} (_92763 : A -> Prop) (_92764 : A -> Prop) (h1 : term104 A) : term471 A _92763 _92764.
Proof. exact (EQ_MP (@lem6966773 A _92763 _92764) (@lem6966772 A _92763 _92764 h1)). Qed.
Lemma lem6966775 {A : Type'} (_92763 : A -> Prop) (_92764 : A -> Prop) (_92765 : A) (h1 : term104 A) : term459 A _92763 _92764 _92765.
Proof. exact (@lem6966774 A _92763 _92764 h1 _92765). Qed.
Lemma lem6966776 {A : Type'} (_92763 : A -> Prop) (_92765 : A) (_92764 : A -> Prop) : (term459 A _92763 _92764 _92765) = (term439 A _92763 _92765 _92764).
Proof. exact (eq_refl (term459 A _92763 _92764 _92765)). Qed.
Lemma lem6966787 {A : Type'} (_92769 : A -> Prop) (h1 : term105 A) : term547 A _92769.
Proof. exact (@lem6966675 A h1 _92769). Qed.
Lemma lem6966788 {A : Type'} (_92769 : A -> Prop) : (term547 A _92769) = (term538 A _92769).
Proof. exact (eq_refl (term547 A _92769)). Qed.
Lemma lem6966789 {A : Type'} (_92769 : A -> Prop) (h1 : term105 A) : term538 A _92769.
Proof. exact (EQ_MP (@lem6966788 A _92769) (@lem6966787 A _92769 h1)). Qed.
Lemma lem6966790 {A : Type'} (_92769 : A -> Prop) (_92770 : A -> Prop) (h1 : term105 A) : term548 A _92769 _92770.
Proof. exact (@lem6966789 A _92769 h1 _92770). Qed.
Lemma lem6966791 {A : Type'} (_92769 : A -> Prop) (_92770 : A -> Prop) : (term548 A _92769 _92770) = (term536 A _92769 _92770).
Proof. exact (eq_refl (term548 A _92769 _92770)). Qed.
Lemma lem6966792 {A : Type'} (_92769 : A -> Prop) (_92770 : A -> Prop) (h1 : term105 A) : term536 A _92769 _92770.
Proof. exact (EQ_MP (@lem6966791 A _92769 _92770) (@lem6966790 A _92769 _92770 h1)). Qed.
Lemma lem6966793 {A : Type'} (_92769 : A -> Prop) (_92770 : A -> Prop) (_92771 : A) (h1 : term105 A) : term549 A _92769 _92770 _92771.
Proof. exact (@lem6966792 A _92769 _92770 h1 _92771). Qed.
Lemma lem6966794 {A : Type'} (_92769 : A -> Prop) (_92771 : A) (_92770 : A -> Prop) : (term549 A _92769 _92770 _92771) = (term533 A _92769 _92771 _92770).
Proof. exact (eq_refl (term549 A _92769 _92770 _92771)). Qed.
Lemma lem6966795 {A : Type'} (_92769 : A -> Prop) (_92771 : A) (_92770 : A -> Prop) (h1 : term105 A) : term533 A _92769 _92771 _92770.
Proof. exact (EQ_MP (@lem6966794 A _92769 _92771 _92770) (@lem6966793 A _92769 _92770 _92771 h1)). Qed.
Lemma lem6966853 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term193 A v u) : term193 A v u.
Proof. exact (h1). Qed.
Lemma lem6966871 {A : Type'} (_92743 : A -> Prop) (_92744 : A) (_92742 : A -> Prop) (h1 : term104 A) : term550 A _92743 _92744 _92742.
Proof. exact (proj1 (@lem6966714 A _92742 _92744 _92743 h1)). Qed.
Lemma lem6966883 {A : Type'} (_92738 : A -> Prop) (_92737 : A -> Prop) (x : type638 A) (h1 : term355 A x) : term551 A x _92738 _92737.
Proof. exact (proj1 (@lem6966696 A _92737 _92738 x h1)). Qed.
Lemma lem6966889 {A : Type'} (_92737 : A -> Prop) (_92738 : A -> Prop) (x : type638 A) (h1 : term355 A x) : term552 A x _92737 _92738.
Proof. exact (proj2 (@lem6966696 A _92737 _92738 x h1)). Qed.
Lemma lem6966902 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (_92754 : A) : (term170 A v u f _92754) = (term553 A v u f _92754).
Proof. exact (@lem6963784 (term16 A _92754 v) (@IN A _92754 u) ((f _92754) = (NUMERAL 0))). Qed.
Lemma lem6966903 {A : Type'} (_92754 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) : term553 A v u f _92754.
Proof. exact (EQ_MP (@lem6966902 A v u f _92754) (@lem6966744 A _92754 v u f h1)). Qed.
Lemma lem6966923 {A : Type'} (_92763 : A -> Prop) (_92765 : A) (_92764 : A -> Prop) (h1 : term104 A) : term439 A _92763 _92765 _92764.
Proof. exact (EQ_MP (@lem6966776 A _92763 _92765 _92764) (@lem6966775 A _92763 _92764 _92765 h1)). Qed.
Lemma lem6966939 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term174 A v u f x') : term16 A x' u.
Proof. exact (proj2 (@lem6966255 A v u f x' h1)). Qed.
Lemma lem6966945 {A : Type'} (_92770 : A -> Prop) (_92771 : A) (_92769 : A -> Prop) (h1 : term105 A) : term554 A _92770 _92771 _92769.
Proof. exact (proj1 (@lem6966795 A _92769 _92771 _92770 h1)). Qed.
Lemma lem6967095 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term193 A v u) : term193 A v u.
Proof. exact (h1). Qed.
Lemma lem6967096 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term193 A v u) : term555 A v u.
Proof. exact (fun h0 : term188 A v u => @lem6967095 A v u h1). Qed.
Lemma lem6967098 (p : Prop) : (term556 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6967099 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term555 A v u) = (term193 A v u).
Proof. exact (@lem6967098 (term188 A v u)). Qed.
Lemma lem6967100 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term193 A v u) : term193 A v u.
Proof. exact (EQ_MP (@lem6967099 A v u) (@lem6967096 A v u h1)). Qed.
Lemma lem6967106 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6967107 {A : Type'} (x : type638 A) (_92737 : A -> Prop) (_92738 : A -> Prop) : (term551 A x _92738 _92737) = (term557 A x _92737 _92738).
Proof. exact (@lem6967106 (term520 A x _92738 _92737) (@SUBSET A _92737 _92738)). Qed.
Lemma lem6967113 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6967114 {A : Type'} (x : type638 A) (_92737 : A -> Prop) (_92738 : A -> Prop) : (term558 A x _92738 _92737) = (term559 A x _92737 _92738).
Proof. exact (MK_COMB (@lem6967113) (@lem6967107 A x _92737 _92738)). Qed.
Lemma lem6967120 {A : Type'} (x : type638 A) (_92737 : A -> Prop) (_92738 : A -> Prop) : (term557 A x _92737 _92738) = (term557 A x _92737 _92738).
Proof. exact (eq_refl (term557 A x _92737 _92738)). Qed.
Lemma lem6967121 {A : Type'} (x : type638 A) (_92737 : A -> Prop) (_92738 : A -> Prop) : ((term551 A x _92738 _92737) = (term557 A x _92737 _92738)) = ((term557 A x _92737 _92738) = (term557 A x _92737 _92738)).
Proof. exact (MK_COMB (@lem6967114 A x _92737 _92738) (@lem6967120 A x _92737 _92738)). Qed.
Lemma lem6967123 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6967124 (x : Prop) : (x = x) = True.
Proof. exact (@lem6967123 Prop x). Qed.
Lemma lem6967125 {A : Type'} (x : type638 A) (_92737 : A -> Prop) (_92738 : A -> Prop) : ((term557 A x _92737 _92738) = (term557 A x _92737 _92738)) = True.
Proof. exact (@lem6967124 (term557 A x _92737 _92738)). Qed.
Lemma lem6967126 {A : Type'} (x : type638 A) (_92737 : A -> Prop) (_92738 : A -> Prop) : ((term551 A x _92738 _92737) = (term557 A x _92737 _92738)) = True.
Proof. exact (TRANS (@lem6967121 A x _92737 _92738) (@lem6967125 A x _92737 _92738)). Qed.
Lemma lem6967127 {A : Type'} (x : type638 A) (_92737 : A -> Prop) (_92738 : A -> Prop) : True = ((term551 A x _92738 _92737) = (term557 A x _92737 _92738)).
Proof. exact (SYM (@lem6967126 A x _92737 _92738)). Qed.
Lemma lem6967128 {A : Type'} (x : type638 A) (_92737 : A -> Prop) (_92738 : A -> Prop) : (term551 A x _92738 _92737) = (term557 A x _92737 _92738).
Proof. exact (EQ_MP (@lem6967127 A x _92737 _92738) (@lem0)). Qed.
Lemma lem6967129 {A : Type'} (_92737 : A -> Prop) (_92738 : A -> Prop) (x : type638 A) (h1 : term355 A x) : term557 A x _92737 _92738.
Proof. exact (EQ_MP (@lem6967128 A x _92737 _92738) (@lem6966883 A _92738 _92737 x h1)). Qed.
Lemma lem6967131 (b : Prop) (a : Prop) : (a \/ b) = (term560 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6967134 {A : Type'} (x : type638 A) (_92738 : A -> Prop) (_92737 : A -> Prop) : (term557 A x _92737 _92738) = (term561 A x _92738 _92737).
Proof. exact (@lem6967131 (@SUBSET A _92737 _92738) (term520 A x _92738 _92737)). Qed.
Lemma lem6967137 {A : Type'} (_92738 : A -> Prop) (_92737 : A -> Prop) (x : type638 A) (h1 : term355 A x) : term561 A x _92738 _92737.
Proof. exact (EQ_MP (@lem6967134 A x _92738 _92737) (@lem6967129 A _92737 _92738 x h1)). Qed.
Lemma lem6967138 {A : Type'} (_92738 : A -> Prop) (_92737 : A -> Prop) (x : type638 A) (h1 : term355 A x) : term561 A x _92738 _92737.
Proof. exact (@lem6967137 A _92738 _92737 x h1). Qed.
Lemma lem6967139 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term355 A x) : term562 A x v u.
Proof. exact (@lem6967138 A (term1 A v u) u x h1). Qed.
Lemma lem6967142 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term193 A v u) (h2 : term355 A x) : term563 A x v u.
Proof. exact (@lem6967139 A v u x h2 (@lem6967100 A v u h1)). Qed.
Lemma lem6967143 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term193 A v u) (h2 : term355 A x) : term564 A x v u.
Proof. exact (fun h0 : term565 A x v u => @lem6967142 A v u x h1 h2). Qed.
Lemma lem6967145 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6967146 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) : (term564 A x v u) = (term563 A x v u).
Proof. exact (@lem6967145 (term563 A x v u)). Qed.
Lemma lem6967147 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term193 A v u) (h2 : term355 A x) : term563 A x v u.
Proof. exact (EQ_MP (@lem6967146 A x v u) (@lem6967143 A v u x h1 h2)). Qed.
Lemma lem6967149 (b : Prop) (a : Prop) : (a \/ b) = (term560 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6967150 {A : Type'} (_92744 : A) (_92742 : A -> Prop) (_92743 : A -> Prop) : (term550 A _92743 _92744 _92742) = (term566 A _92744 _92742 _92743).
Proof. exact (@lem6967149 (term16 A _92744 _92742) (term3 A _92744 _92742 _92743)). Qed.
Lemma lem6967152 (a : Prop) : (term30 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6967153 {A : Type'} (_92744 : A) (_92742 : A -> Prop) : (term162 A _92744 _92742) = (@IN A _92744 _92742).
Proof. exact (@lem6967152 (@IN A _92744 _92742)). Qed.
Lemma lem6967154 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6967155 {A : Type'} (_92744 : A) (_92742 : A -> Prop) : (term567 A _92744 _92742) = (term568 A _92744 _92742).
Proof. exact (MK_COMB (@lem6967154) (@lem6967153 A _92744 _92742)). Qed.
Lemma lem6967156 {A : Type'} (_92744 : A) (_92742 : A -> Prop) (_92743 : A -> Prop) : (term3 A _92744 _92742 _92743) = (term3 A _92744 _92742 _92743).
Proof. exact (eq_refl (term3 A _92744 _92742 _92743)). Qed.
Lemma lem6967157 {A : Type'} (_92744 : A) (_92742 : A -> Prop) (_92743 : A -> Prop) : (term566 A _92744 _92742 _92743) = (term569 A _92744 _92742 _92743).
Proof. exact (MK_COMB (@lem6967155 A _92744 _92742) (@lem6967156 A _92744 _92742 _92743)). Qed.
Lemma lem6967158 {A : Type'} (_92744 : A) (_92742 : A -> Prop) (_92743 : A -> Prop) : (term550 A _92743 _92744 _92742) = (term569 A _92744 _92742 _92743).
Proof. exact (TRANS (@lem6967150 A _92744 _92742 _92743) (@lem6967157 A _92744 _92742 _92743)). Qed.
Lemma lem6967161 {A : Type'} (_92744 : A) (_92742 : A -> Prop) (_92743 : A -> Prop) (h1 : term104 A) : term569 A _92744 _92742 _92743.
Proof. exact (EQ_MP (@lem6967158 A _92744 _92742 _92743) (@lem6966871 A _92743 _92744 _92742 h1)). Qed.
Lemma lem6967162 {A : Type'} (_92744 : A) (_92742 : A -> Prop) (_92743 : A -> Prop) (h1 : term104 A) : term569 A _92744 _92742 _92743.
Proof. exact (@lem6967161 A _92744 _92742 _92743 h1). Qed.
Lemma lem6967163 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (_92743 : A -> Prop) (h1 : term104 A) : term570 A x v u _92743.
Proof. exact (@lem6967162 A (term571 A x v u) u _92743 h1). Qed.
Lemma lem6967166 {A : Type'} (_92743 : A -> Prop) (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term193 A v u) (h3 : term355 A x) : term572 A x v u _92743.
Proof. exact (@lem6967163 A x v u _92743 h1 (@lem6967147 A v u x h2 h3)). Qed.
Lemma lem6967167 {A : Type'} (_92743 : A -> Prop) (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term193 A v u) (h3 : term355 A x) : term572 A x v u _92743.
Proof. exact (@lem6967166 A _92743 v u x h1 h2 h3). Qed.
Lemma lem6967168 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term193 A v u) (h3 : term355 A x) : term573 A x v u.
Proof. exact (@lem6967167 A (@DIFF A v u) v u x h1 h2 h3). Qed.
Lemma lem6967169 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term193 A v u) (h3 : term355 A x) : term574 A x v u.
Proof. exact (fun h0 : term575 A x v u => @lem6967168 A v u x h1 h2 h3). Qed.
Lemma lem6967171 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6967172 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) : (term574 A x v u) = (term573 A x v u).
Proof. exact (@lem6967171 (term573 A x v u)). Qed.
Lemma lem6967173 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term193 A v u) (h3 : term355 A x) : term573 A x v u.
Proof. exact (EQ_MP (@lem6967172 A x v u) (@lem6967169 A v u x h1 h2 h3)). Qed.
Lemma lem6967175 (b : Prop) (a : Prop) : (a \/ b) = (term560 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6967176 {A : Type'} (x : type638 A) (_92737 : A -> Prop) (_92738 : A -> Prop) : (term552 A x _92737 _92738) = (term576 A x _92737 _92738).
Proof. exact (@lem6967175 (term521 A x _92737 _92738) (@SUBSET A _92737 _92738)). Qed.
Lemma lem6967178 (a : Prop) : (term30 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6967179 {A : Type'} (x : type638 A) (_92737 : A -> Prop) (_92738 : A -> Prop) : (term577 A x _92737 _92738) = (term578 A x _92737 _92738).
Proof. exact (@lem6967178 (term578 A x _92737 _92738)). Qed.
Lemma lem6967180 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6967181 {A : Type'} (x : type638 A) (_92737 : A -> Prop) (_92738 : A -> Prop) : (term579 A x _92737 _92738) = (term580 A x _92737 _92738).
Proof. exact (MK_COMB (@lem6967180) (@lem6967179 A x _92737 _92738)). Qed.
Lemma lem6967182 {A : Type'} (_92737 : A -> Prop) (_92738 : A -> Prop) : (@SUBSET A _92737 _92738) = (@SUBSET A _92737 _92738).
Proof. exact (eq_refl (@SUBSET A _92737 _92738)). Qed.
Lemma lem6967183 {A : Type'} (x : type638 A) (_92737 : A -> Prop) (_92738 : A -> Prop) : (term576 A x _92737 _92738) = (term581 A x _92737 _92738).
Proof. exact (MK_COMB (@lem6967181 A x _92737 _92738) (@lem6967182 A _92737 _92738)). Qed.
Lemma lem6967184 {A : Type'} (x : type638 A) (_92737 : A -> Prop) (_92738 : A -> Prop) : (term552 A x _92737 _92738) = (term581 A x _92737 _92738).
Proof. exact (TRANS (@lem6967176 A x _92737 _92738) (@lem6967183 A x _92737 _92738)). Qed.
Lemma lem6967187 {A : Type'} (_92737 : A -> Prop) (_92738 : A -> Prop) (x : type638 A) (h1 : term355 A x) : term581 A x _92737 _92738.
Proof. exact (EQ_MP (@lem6967184 A x _92737 _92738) (@lem6966889 A _92737 _92738 x h1)). Qed.
Lemma lem6967188 {A : Type'} (_92737 : A -> Prop) (_92738 : A -> Prop) (x : type638 A) (h1 : term355 A x) : term581 A x _92737 _92738.
Proof. exact (@lem6967187 A _92737 _92738 x h1). Qed.
Lemma lem6967189 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term355 A x) : term582 A x v u.
Proof. exact (@lem6967188 A u (term1 A v u) x h1). Qed.
Lemma lem6967192 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term193 A v u) (h3 : term355 A x) : term188 A v u.
Proof. exact (@lem6967189 A v u x h3 (@lem6967173 A v u x h1 h2 h3)). Qed.
Lemma lem6967193 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term355 A x) : term583 A v u.
Proof. exact (fun h0 : term193 A v u => @lem6967192 A v u x h1 h0 h2). Qed.
Lemma lem6967195 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6967196 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term583 A v u) = (term188 A v u).
Proof. exact (@lem6967195 (term188 A v u)). Qed.
Lemma lem6967197 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term355 A x) : term188 A v u.
Proof. exact (EQ_MP (@lem6967196 A v u) (@lem6967193 A v u x h1 h2)). Qed.
Lemma lem6967200 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6967202 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term193 A v u) = (term584 A v u).
Proof. exact (@lem6967200 (term188 A v u)). Qed.
Lemma lem6967205 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term193 A v u) : term584 A v u.
Proof. exact (EQ_MP (@lem6967202 A v u) (@lem6966853 A v u h1)). Qed.
Lemma lem6967208 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term193 A v u) (h3 : term355 A x) : False.
Proof. exact (@lem6967205 A v u h2 (@lem6967197 A v u x h1 h3)). Qed.
Lemma lem6967209 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term193 A v u) (h3 : term355 A x) : term66.
Proof. exact (fun h0 : ~ False => @lem6967208 A v u x h1 h2 h3). Qed.
Lemma lem6967211 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6967212 : term66 = False.
Proof. exact (@lem6967211 False). Qed.
Lemma lem6967213 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term193 A v u) (h3 : term355 A x) : False.
Proof. exact (EQ_MP (@lem6967212) (@lem6967209 A v u x h1 h2 h3)). Qed.
Lemma lem6967332 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term174 A v u f x') : term10 A x' v u.
Proof. exact (proj1 (@lem6966255 A v u f x' h1)). Qed.
Lemma lem6967333 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term174 A v u f x') : term585 A x' v u.
Proof. exact (fun h0 : term586 A x' v u => @lem6967332 A v u f x' h1). Qed.
Lemma lem6967335 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6967336 {A : Type'} (x' : A) (v : A -> Prop) (u : A -> Prop) : (term585 A x' v u) = (term10 A x' v u).
Proof. exact (@lem6967335 (term10 A x' v u)). Qed.
Lemma lem6967337 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term174 A v u f x') : term10 A x' v u.
Proof. exact (EQ_MP (@lem6967336 A x' v u) (@lem6967333 A v u f x' h1)). Qed.
Lemma lem6967340 {A : Type'} (x' : A) (u : A -> Prop) (h1 : term16 A x' u) : term16 A x' u.
Proof. exact (h1). Qed.
Lemma lem6967341 {A : Type'} (x' : A) (u : A -> Prop) (h1 : term16 A x' u) : term587 A x' u.
Proof. exact (fun h0 : @IN A x' u => @lem6967340 A x' u h1). Qed.
Lemma lem6967343 (p : Prop) : (term556 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6967344 {A : Type'} (x' : A) (u : A -> Prop) : (term587 A x' u) = (term16 A x' u).
Proof. exact (@lem6967343 (@IN A x' u)). Qed.
Lemma lem6967345 {A : Type'} (x' : A) (u : A -> Prop) (h1 : term16 A x' u) : term16 A x' u.
Proof. exact (EQ_MP (@lem6967344 A x' u) (@lem6967341 A x' u h1)). Qed.
Lemma lem6967347 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term174 A v u f x') : term588 A f x'.
Proof. exact (proj2 (@lem6966253 A v u f x' h1)). Qed.
Lemma lem6967348 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term174 A v u f x') : term589 A f x'.
Proof. exact (fun h0 : (f x') = (NUMERAL 0) => @lem6967347 A v u f x' h1). Qed.
Lemma lem6967350 (p : Prop) : (term556 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6967351 {A : Type'} (f : A -> nat) (x' : A) : (term589 A f x') = (term588 A f x').
Proof. exact (@lem6967350 ((f x') = (NUMERAL 0))). Qed.
Lemma lem6967352 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term174 A v u f x') : term588 A f x'.
Proof. exact (EQ_MP (@lem6967351 A f x') (@lem6967348 A v u f x' h1)). Qed.
Lemma lem6967354 (b : Prop) (a : Prop) : (a \/ b) = (term560 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6967355 {A : Type'} (u : A -> Prop) (f : A -> nat) (_92754 : A) (v : A -> Prop) : (term553 A v u f _92754) = (term590 A u f _92754 v).
Proof. exact (@lem6967354 (term591 A u f _92754) (term16 A _92754 v)). Qed.
Lemma lem6967357 (a : Prop) (b : Prop) : (term592 a b) = (term593 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6967358 {A : Type'} (u : A -> Prop) (f : A -> nat) (_92754 : A) : (term594 A u f _92754) = (term595 A u f _92754).
Proof. exact (@lem6967357 (@IN A _92754 u) ((f _92754) = (NUMERAL 0))). Qed.
Lemma lem6967359 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6967360 {A : Type'} (u : A -> Prop) (f : A -> nat) (_92754 : A) : (term596 A u f _92754) = (term597 A u f _92754).
Proof. exact (MK_COMB (@lem6967359) (@lem6967358 A u f _92754)). Qed.
Lemma lem6967361 {A : Type'} (_92754 : A) (v : A -> Prop) : (term16 A _92754 v) = (term16 A _92754 v).
Proof. exact (eq_refl (term16 A _92754 v)). Qed.
Lemma lem6967362 {A : Type'} (u : A -> Prop) (f : A -> nat) (_92754 : A) (v : A -> Prop) : (term590 A u f _92754 v) = (term598 A u f _92754 v).
Proof. exact (MK_COMB (@lem6967360 A u f _92754) (@lem6967361 A _92754 v)). Qed.
Lemma lem6967363 {A : Type'} (u : A -> Prop) (f : A -> nat) (_92754 : A) (v : A -> Prop) : (term553 A v u f _92754) = (term598 A u f _92754 v).
Proof. exact (TRANS (@lem6967355 A u f _92754 v) (@lem6967362 A u f _92754 v)). Qed.
Lemma lem6967365 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term16 A x' u) (h2 : term174 A v u f x') : term595 A u f x'.
Proof. exact (conj (@lem6967345 A x' u h1) (@lem6967352 A v u f x' h2)). Qed.
Lemma lem6967367 {A : Type'} (_92754 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) : term598 A u f _92754 v.
Proof. exact (EQ_MP (@lem6967363 A u f _92754 v) (@lem6966903 A _92754 v u f h1)). Qed.
Lemma lem6967368 {A : Type'} (_92754 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) : term598 A u f _92754 v.
Proof. exact (@lem6967367 A _92754 v u f h1). Qed.
Lemma lem6967369 {A : Type'} (x' : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) : term598 A u f x' v.
Proof. exact (@lem6967368 A x' v u f h1). Qed.
Lemma lem6967372 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term16 A x' u) (h3 : term174 A v u f x') : term16 A x' v.
Proof. exact (@lem6967369 A x' v u f h1 (@lem6967365 A v u f x' h2 h3)). Qed.
Lemma lem6967373 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term16 A x' u) (h3 : term174 A v u f x') : term587 A x' v.
Proof. exact (fun h0 : @IN A x' v => @lem6967372 A v u f x' h1 h2 h3). Qed.
Lemma lem6967375 (p : Prop) : (term556 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6967376 {A : Type'} (x' : A) (v : A -> Prop) : (term587 A x' v) = (term16 A x' v).
Proof. exact (@lem6967375 (@IN A x' v)). Qed.
Lemma lem6967377 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term16 A x' u) (h3 : term174 A v u f x') : term16 A x' v.
Proof. exact (EQ_MP (@lem6967376 A x' v) (@lem6967373 A v u f x' h1 h2 h3)). Qed.
Lemma lem6967379 (b : Prop) (a : Prop) : (a \/ b) = (term560 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6967382 {A : Type'} (_92771 : A) (_92769 : A -> Prop) (_92770 : A -> Prop) : (term554 A _92770 _92771 _92769) = (term599 A _92771 _92769 _92770).
Proof. exact (@lem6967379 (@IN A _92771 _92769) (term534 A _92771 _92769 _92770)). Qed.
Lemma lem6967385 {A : Type'} (_92771 : A) (_92769 : A -> Prop) (_92770 : A -> Prop) (h1 : term105 A) : term599 A _92771 _92769 _92770.
Proof. exact (EQ_MP (@lem6967382 A _92771 _92769 _92770) (@lem6966945 A _92770 _92771 _92769 h1)). Qed.
Lemma lem6967386 {A : Type'} (_92771 : A) (_92769 : A -> Prop) (_92770 : A -> Prop) (h1 : term105 A) : term599 A _92771 _92769 _92770.
Proof. exact (@lem6967385 A _92771 _92769 _92770 h1). Qed.
Lemma lem6967387 {A : Type'} (x' : A) (v : A -> Prop) (_92770 : A -> Prop) (h1 : term105 A) : term599 A x' v _92770.
Proof. exact (@lem6967386 A x' v _92770 h1). Qed.
Lemma lem6967390 {A : Type'} (_92770 : A -> Prop) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term16 A x' u) (h4 : term174 A v u f x') : term534 A x' v _92770.
Proof. exact (@lem6967387 A x' v _92770 h2 (@lem6967377 A v u f x' h1 h3 h4)). Qed.
Lemma lem6967391 {A : Type'} (_92770 : A -> Prop) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term16 A x' u) (h4 : term174 A v u f x') : term534 A x' v _92770.
Proof. exact (@lem6967390 A _92770 v u f x' h1 h2 h3 h4). Qed.
Lemma lem6967392 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term16 A x' u) (h4 : term174 A v u f x') : term534 A x' v u.
Proof. exact (@lem6967391 A u v u f x' h1 h2 h3 h4). Qed.
Lemma lem6967393 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term16 A x' u) (h4 : term174 A v u f x') : term600 A x' v u.
Proof. exact (fun h0 : term12 A x' v u => @lem6967392 A v u f x' h1 h2 h3 h4). Qed.
Lemma lem6967395 (p : Prop) : (term556 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6967396 {A : Type'} (x' : A) (v : A -> Prop) (u : A -> Prop) : (term600 A x' v u) = (term534 A x' v u).
Proof. exact (@lem6967395 (term12 A x' v u)). Qed.
Lemma lem6967397 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term16 A x' u) (h4 : term174 A v u f x') : term534 A x' v u.
Proof. exact (EQ_MP (@lem6967396 A x' v u) (@lem6967393 A v u f x' h1 h2 h3 h4)). Qed.
Lemma lem6967403 (q : Prop) (p : Prop) (r : Prop) : (term74 p q r) = (term74 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6967404 {A : Type'} (_92763 : A -> Prop) (_92765 : A) (_92764 : A -> Prop) : (term439 A _92763 _92765 _92764) = (term601 A _92763 _92765 _92764).
Proof. exact (@lem6967403 (@IN A _92765 _92763) (term602 A _92765 _92763 _92764) (@IN A _92765 _92764)). Qed.
Lemma lem6967418 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6967419 {A : Type'} (_92765 : A) (_92763 : A -> Prop) (_92764 : A -> Prop) : (term603 A _92763 _92765 _92764) = (term604 A _92765 _92763 _92764).
Proof. exact (@lem6967418 (@IN A _92765 _92764) (term602 A _92765 _92763 _92764)). Qed.
Lemma lem6967425 {A : Type'} (_92765 : A) (_92763 : A -> Prop) : (term5 A _92765 _92763) = (term5 A _92765 _92763).
Proof. exact (eq_refl (term5 A _92765 _92763)). Qed.
Lemma lem6967426 {A : Type'} (_92765 : A) (_92763 : A -> Prop) (_92764 : A -> Prop) : (term601 A _92763 _92765 _92764) = (term605 A _92765 _92763 _92764).
Proof. exact (MK_COMB (@lem6967425 A _92765 _92763) (@lem6967419 A _92765 _92763 _92764)). Qed.
Lemma lem6967437 {A : Type'} (_92765 : A) (_92763 : A -> Prop) (_92764 : A -> Prop) : (term439 A _92763 _92765 _92764) = (term605 A _92765 _92763 _92764).
Proof. exact (TRANS (@lem6967404 A _92763 _92765 _92764) (@lem6967426 A _92765 _92763 _92764)). Qed.
Lemma lem6967438 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6967439 {A : Type'} (_92765 : A) (_92763 : A -> Prop) (_92764 : A -> Prop) : (term606 A _92763 _92765 _92764) = (term607 A _92765 _92763 _92764).
Proof. exact (MK_COMB (@lem6967438) (@lem6967437 A _92765 _92763 _92764)). Qed.
Lemma lem6967453 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6967454 {A : Type'} (_92765 : A) (_92763 : A -> Prop) (_92764 : A -> Prop) : (term603 A _92763 _92765 _92764) = (term604 A _92765 _92763 _92764).
Proof. exact (@lem6967453 (@IN A _92765 _92764) (term602 A _92765 _92763 _92764)). Qed.
Lemma lem6967460 {A : Type'} (_92765 : A) (_92763 : A -> Prop) : (term5 A _92765 _92763) = (term5 A _92765 _92763).
Proof. exact (eq_refl (term5 A _92765 _92763)). Qed.
Lemma lem6967461 {A : Type'} (_92765 : A) (_92763 : A -> Prop) (_92764 : A -> Prop) : (term601 A _92763 _92765 _92764) = (term605 A _92765 _92763 _92764).
Proof. exact (MK_COMB (@lem6967460 A _92765 _92763) (@lem6967454 A _92765 _92763 _92764)). Qed.
Lemma lem6967472 {A : Type'} (_92765 : A) (_92763 : A -> Prop) (_92764 : A -> Prop) : ((term439 A _92763 _92765 _92764) = (term601 A _92763 _92765 _92764)) = ((term605 A _92765 _92763 _92764) = (term605 A _92765 _92763 _92764)).
Proof. exact (MK_COMB (@lem6967439 A _92765 _92763 _92764) (@lem6967461 A _92765 _92763 _92764)). Qed.
Lemma lem6967474 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6967475 (x : Prop) : (x = x) = True.
Proof. exact (@lem6967474 Prop x). Qed.
Lemma lem6967476 {A : Type'} (_92765 : A) (_92763 : A -> Prop) (_92764 : A -> Prop) : ((term605 A _92765 _92763 _92764) = (term605 A _92765 _92763 _92764)) = True.
Proof. exact (@lem6967475 (term605 A _92765 _92763 _92764)). Qed.
Lemma lem6967477 {A : Type'} (_92763 : A -> Prop) (_92765 : A) (_92764 : A -> Prop) : ((term439 A _92763 _92765 _92764) = (term601 A _92763 _92765 _92764)) = True.
Proof. exact (TRANS (@lem6967472 A _92765 _92763 _92764) (@lem6967476 A _92765 _92763 _92764)). Qed.
Lemma lem6967478 {A : Type'} (_92763 : A -> Prop) (_92765 : A) (_92764 : A -> Prop) : True = ((term439 A _92763 _92765 _92764) = (term601 A _92763 _92765 _92764)).
Proof. exact (SYM (@lem6967477 A _92763 _92765 _92764)). Qed.
Lemma lem6967479 {A : Type'} (_92763 : A -> Prop) (_92765 : A) (_92764 : A -> Prop) : (term439 A _92763 _92765 _92764) = (term601 A _92763 _92765 _92764).
Proof. exact (EQ_MP (@lem6967478 A _92763 _92765 _92764) (@lem0)). Qed.
Lemma lem6967480 {A : Type'} (_92763 : A -> Prop) (_92765 : A) (_92764 : A -> Prop) (h1 : term104 A) : term601 A _92763 _92765 _92764.
Proof. exact (EQ_MP (@lem6967479 A _92763 _92765 _92764) (@lem6966923 A _92763 _92765 _92764 h1)). Qed.
Lemma lem6967482 (b : Prop) (a : Prop) : (a \/ b) = (term560 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6967483 {A : Type'} (_92764 : A -> Prop) (_92765 : A) (_92763 : A -> Prop) : (term601 A _92763 _92765 _92764) = (term608 A _92764 _92765 _92763).
Proof. exact (@lem6967482 (term603 A _92763 _92765 _92764) (@IN A _92765 _92763)). Qed.
Lemma lem6967485 (a : Prop) (b : Prop) : (term592 a b) = (term593 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6967486 {A : Type'} (_92763 : A -> Prop) (_92765 : A) (_92764 : A -> Prop) : (term609 A _92763 _92765 _92764) = (term610 A _92763 _92765 _92764).
Proof. exact (@lem6967485 (term602 A _92765 _92763 _92764) (@IN A _92765 _92764)). Qed.
Lemma lem6967488 (a : Prop) : (term30 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6967489 {A : Type'} (_92765 : A) (_92763 : A -> Prop) (_92764 : A -> Prop) : (term611 A _92765 _92763 _92764) = (term3 A _92765 _92763 _92764).
Proof. exact (@lem6967488 (term3 A _92765 _92763 _92764)). Qed.
Lemma lem6967490 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6967491 {A : Type'} (_92765 : A) (_92763 : A -> Prop) (_92764 : A -> Prop) : (term612 A _92765 _92763 _92764) = (term613 A _92765 _92763 _92764).
Proof. exact (MK_COMB (@lem6967490) (@lem6967489 A _92765 _92763 _92764)). Qed.
Lemma lem6967492 {A : Type'} (_92765 : A) (_92764 : A -> Prop) : (term16 A _92765 _92764) = (term16 A _92765 _92764).
Proof. exact (eq_refl (term16 A _92765 _92764)). Qed.
Lemma lem6967493 {A : Type'} (_92763 : A -> Prop) (_92765 : A) (_92764 : A -> Prop) : (term610 A _92763 _92765 _92764) = (term614 A _92763 _92765 _92764).
Proof. exact (MK_COMB (@lem6967491 A _92765 _92763 _92764) (@lem6967492 A _92765 _92764)). Qed.
Lemma lem6967494 {A : Type'} (_92763 : A -> Prop) (_92765 : A) (_92764 : A -> Prop) : (term609 A _92763 _92765 _92764) = (term614 A _92763 _92765 _92764).
Proof. exact (TRANS (@lem6967486 A _92763 _92765 _92764) (@lem6967493 A _92763 _92765 _92764)). Qed.
Lemma lem6967495 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6967496 {A : Type'} (_92763 : A -> Prop) (_92765 : A) (_92764 : A -> Prop) : (term615 A _92763 _92765 _92764) = (term616 A _92763 _92765 _92764).
Proof. exact (MK_COMB (@lem6967495) (@lem6967494 A _92763 _92765 _92764)). Qed.
Lemma lem6967497 {A : Type'} (_92765 : A) (_92763 : A -> Prop) : (@IN A _92765 _92763) = (@IN A _92765 _92763).
Proof. exact (eq_refl (@IN A _92765 _92763)). Qed.
Lemma lem6967498 {A : Type'} (_92764 : A -> Prop) (_92765 : A) (_92763 : A -> Prop) : (term608 A _92764 _92765 _92763) = (term617 A _92764 _92765 _92763).
Proof. exact (MK_COMB (@lem6967496 A _92763 _92765 _92764) (@lem6967497 A _92765 _92763)). Qed.
Lemma lem6967499 {A : Type'} (_92764 : A -> Prop) (_92765 : A) (_92763 : A -> Prop) : (term601 A _92763 _92765 _92764) = (term617 A _92764 _92765 _92763).
Proof. exact (TRANS (@lem6967483 A _92764 _92765 _92763) (@lem6967498 A _92764 _92765 _92763)). Qed.
Lemma lem6967501 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term16 A x' u) (h4 : term174 A v u f x') : term618 A x' v u.
Proof. exact (conj (@lem6967337 A v u f x' h4) (@lem6967397 A v u f x' h1 h2 h3 h4)). Qed.
Lemma lem6967503 {A : Type'} (_92764 : A -> Prop) (_92765 : A) (_92763 : A -> Prop) (h1 : term104 A) : term617 A _92764 _92765 _92763.
Proof. exact (EQ_MP (@lem6967499 A _92764 _92765 _92763) (@lem6967480 A _92763 _92765 _92764 h1)). Qed.
Lemma lem6967504 {A : Type'} (_92764 : A -> Prop) (_92765 : A) (_92763 : A -> Prop) (h1 : term104 A) : term617 A _92764 _92765 _92763.
Proof. exact (@lem6967503 A _92764 _92765 _92763 h1). Qed.
Lemma lem6967505 {A : Type'} (v : A -> Prop) (x' : A) (u : A -> Prop) (h1 : term104 A) : term619 A v x' u.
Proof. exact (@lem6967504 A (@DIFF A v u) x' u h1). Qed.
Lemma lem6967508 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term16 A x' u) (h5 : term174 A v u f x') : @IN A x' u.
Proof. exact (@lem6967505 A v x' u h3 (@lem6967501 A v u f x' h1 h2 h4 h5)). Qed.
Lemma lem6967509 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term174 A v u f x') : term620 A x' u.
Proof. exact (fun h0 : term16 A x' u => @lem6967508 A v u f x' h1 h2 h3 h0 h4). Qed.
Lemma lem6967511 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6967512 {A : Type'} (x' : A) (u : A -> Prop) : (term620 A x' u) = (@IN A x' u).
Proof. exact (@lem6967511 (@IN A x' u)). Qed.
Lemma lem6967513 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term174 A v u f x') : @IN A x' u.
Proof. exact (EQ_MP (@lem6967512 A x' u) (@lem6967509 A v u f x' h1 h2 h3 h4)). Qed.
Lemma lem6967516 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6967518 {A : Type'} (x' : A) (u : A -> Prop) : (term16 A x' u) = (term621 A x' u).
Proof. exact (@lem6967516 (@IN A x' u)). Qed.
Lemma lem6967521 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term174 A v u f x') : term621 A x' u.
Proof. exact (EQ_MP (@lem6967518 A x' u) (@lem6966939 A v u f x' h1)). Qed.
Lemma lem6967524 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term174 A v u f x') : False.
Proof. exact (@lem6967521 A v u f x' h4 (@lem6967513 A v u f x' h1 h2 h3 h4)). Qed.
Lemma lem6967525 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term174 A v u f x') : term66.
Proof. exact (fun h0 : ~ False => @lem6967524 A v u f x' h1 h2 h3 h4). Qed.
Lemma lem6967527 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6967528 : term66 = False.
Proof. exact (@lem6967527 False). Qed.
Lemma lem6967529 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term174 A v u f x') : False.
Proof. exact (EQ_MP (@lem6967528) (@lem6967525 A v u f x' h1 h2 h3 h4)). Qed.
Lemma lem6967530 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term193 A v u) (h3 : term355 A x) : (term193 A v u) = False.
Proof. exact (prop_ext (fun h4 : term193 A v u => @lem6967213 A v u x h1 h2 h3) (fun h4 : False => @lem6966853 A v u h2)). Qed.
Lemma lem6967531 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term193 A v u) (h3 : term355 A x) : False.
Proof. exact (EQ_MP (@lem6967530 A v u x h1 h2 h3) (@lem6966853 A v u h2)). Qed.
Lemma lem6967532 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term193 A v u) (h3 : term355 A x) : (term193 A v u) = False.
Proof. exact (prop_ext (fun h4 : term193 A v u => @lem6967531 A v u x h1 h2 h3) (fun h4 : False => @lem6966468 A v u h2)). Qed.
Lemma lem6967533 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term193 A v u) (h3 : term355 A x) : False.
Proof. exact (EQ_MP (@lem6967532 A v u x h1 h2 h3) (@lem6966468 A v u h2)). Qed.
Lemma lem6967534 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term193 A v u) (h3 : term355 A x) : (term193 A v u) = False.
Proof. exact (prop_ext (fun h4 : term193 A v u => @lem6967533 A v u x h1 h2 h3) (fun h4 : False => @lem6966468 A v u h2)). Qed.
Lemma lem6967535 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term193 A v u) (h3 : term355 A x) : False.
Proof. exact (EQ_MP (@lem6967534 A v u x h1 h2 h3) (@lem6966468 A v u h2)). Qed.
Lemma lem6967536 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term355 A x) (h5 : term200 A v u f x') : False.
Proof. exact (or_elim (@lem6966245 A v u f x' h5) (fun h0 : term193 A v u => @lem6967535 A v u x h3 h0 h4) (fun h0 : term174 A v u f x' => @lem6967529 A v u f x' h1 h2 h3 h0)). Qed.
Lemma lem6967537 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term355 A x) (h5 : term200 A v u f x') : (term200 A v u f x') = False.
Proof. exact (prop_ext (fun h6 : term200 A v u f x' => @lem6967536 A x v u f x' h1 h2 h3 h4 h5) (fun h6 : False => @lem6966245 A v u f x' h5)). Qed.
Lemma lem6967538 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term355 A x) (h5 : term200 A v u f x') : False.
Proof. exact (EQ_MP (@lem6967537 A x v u f x' h1 h2 h3 h4 h5) (@lem6966245 A v u f x' h5)). Qed.
Lemma lem6967539 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term355 A x) (h5 : term200 A v u f x') : (term355 A x) = False.
Proof. exact (prop_ext (fun h6 : term355 A x => @lem6967538 A x v u f x' h1 h2 h3 h4 h5) (fun h6 : False => @lem6966189 A x h4)). Qed.
Lemma lem6967540 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term355 A x) (h5 : term200 A v u f x') : False.
Proof. exact (EQ_MP (@lem6967539 A x v u f x' h1 h2 h3 h4 h5) (@lem6966189 A x h4)). Qed.
Lemma lem6967541 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : type638 A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term103 A v u f) (h5 : term355 A x) : False.
Proof. exact (ex_elim (@lem6964405 A v u f h4) (fun x' : A => fun h0 : term202 A v u f x' => @lem6967540 A x v u f x' h1 h2 h3 h5 h0)). Qed.
Lemma lem6967542 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term106 A) (h5 : term103 A v u f) : False.
Proof. exact (ex_elim (@lem6965025 A h4) (fun x : type638 A => fun h0 : term357 A x => @lem6967541 A v u f x h1 h2 h3 h5 h0)). Qed.
Lemma lem6967543 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term106 A) (h4 : term103 A v u f) : term111 A.
Proof. exact (fun h0 : term104 A => @lem6967542 A v u f h1 h2 h0 h3 h4). Qed.
Lemma lem6967544 {A : Type'} : (term111 A) = (term112 A).
Proof. exact (@lem69 (term104 A)). Qed.
Lemma lem6967545 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term106 A) (h4 : term103 A v u f) : term112 A.
Proof. exact (EQ_MP (@lem6967544 A) (@lem6967543 A v u f h1 h2 h3 h4)). Qed.
Lemma lem6967546 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) (h2 : term106 A) (h3 : term103 A v u f) : term115 A.
Proof. exact (fun h0 : term105 A => @lem6967545 A v u f h1 h0 h2 h3). Qed.
Lemma lem6967547 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) (h2 : term103 A v u f) : term118 A.
Proof. exact (fun h0 : term106 A => @lem6967546 A v u f h1 h0 h2). Qed.
Lemma lem6967548 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) : term121 A v u f.
Proof. exact (fun h0 : term103 A v u f => @lem6967547 A v u f h1 h0). Qed.
Lemma lem6967549 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term124 A v u f.
Proof. exact (fun h0 : term93 A v u f => @lem6967548 A v u f h0). Qed.
Lemma lem6967550 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term126 A v u f.
Proof. exact (fun h0 : @FINITE A u => @lem6967549 A v u f). Qed.
Lemma lem6967555 {A : Type'} (u : A -> Prop) (f : A -> nat) : term130 A u f.
Proof. exact (fun v : A -> Prop => @lem6967550 A v u f). Qed.
Lemma lem6967560 {A : Type'} (f : A -> nat) : term134 A f.
Proof. exact (fun u : A -> Prop => @lem6967555 A u f). Qed.
Lemma lem6967565 {A : Type'} : term138 A.
Proof. exact (fun f : A -> nat => @lem6967560 A f). Qed.
Lemma lem6967566 {A : Type'} : term137 A.
Proof. exact (EQ_MP (@lem6964223 A) (@lem6967565 A)). Qed.
Lemma lem6967567 {A : Type'} (f : A -> nat) : term622 A f.
Proof. exact (@lem6967566 A f). Qed.
Lemma lem6967568 {A : Type'} (f : A -> nat) : (term622 A f) = (term133 A f).
Proof. exact (eq_refl (term622 A f)). Qed.
Lemma lem6967569 {A : Type'} (f : A -> nat) : term133 A f.
Proof. exact (EQ_MP (@lem6967568 A f) (@lem6967567 A f)). Qed.
Lemma lem6967570 {A : Type'} (f : A -> nat) (u : A -> Prop) : term623 A f u.
Proof. exact (@lem6967569 A f u). Qed.
Lemma lem6967571 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term623 A f u) = (term129 A u f).
Proof. exact (eq_refl (term623 A f u)). Qed.
Lemma lem6967572 {A : Type'} (u : A -> Prop) (f : A -> nat) : term129 A u f.
Proof. exact (EQ_MP (@lem6967571 A u f) (@lem6967570 A f u)). Qed.
Lemma lem6967573 {A : Type'} (u : A -> Prop) (f : A -> nat) (v : A -> Prop) : term624 A u f v.
Proof. exact (@lem6967572 A u f v). Qed.
Lemma lem6967574 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term624 A u f v) = (term107 A v u f).
Proof. exact (eq_refl (term624 A u f v)). Qed.
Lemma lem6967575 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term107 A v u f.
Proof. exact (EQ_MP (@lem6967574 A v u f) (@lem6967573 A u f v)). Qed.
Lemma lem6967577 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term107 A v u f.
Proof. exact (@lem6963862 A v u f (@lem6967575 A v u f)). Qed.
Lemma lem6967578 {A : Type'} (v : A -> Prop) (f : A -> nat) (u : A -> Prop) (h1 : @FINITE A u) : term123 A v u f.
Proof. exact (@lem6967577 A v u f (@lem6963817 A u h1)). Qed.
Lemma lem6967579 {A : Type'} (v : A -> Prop) (f : A -> nat) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : term120 A v u f.
Proof. exact (@lem6967578 A v f u h2 (@lem6963816 A v u f h1)). Qed.
Lemma lem6967580 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) (h2 : @FINITE A u) (h3 : term103 A v u f) : term117 A.
Proof. exact (@lem6967579 A v f u h1 h2 (@lem6963840 A v u f h3)). Qed.
Lemma lem6967581 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) (h2 : @FINITE A u) (h3 : term103 A v u f) : term114 A.
Proof. exact (@lem6967580 A v u f h1 h2 h3 (@lem6963845 A)). Qed.
Lemma lem6967582 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) (h2 : @FINITE A u) (h3 : term103 A v u f) : term111 A.
Proof. exact (@lem6967581 A v u f h1 h2 h3 (@lem6963843 A)). Qed.
Lemma lem6967583 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) (h2 : @FINITE A u) (h3 : term103 A v u f) : False.
Proof. exact (@lem6967582 A v u f h1 h2 h3 (@lem6963841 A)). Qed.
Lemma lem6967584 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) (h2 : @FINITE A u) (h3 : term103 A v u f) : (term103 A v u f) = False.
Proof. exact (prop_ext (fun h4 : term103 A v u f => @lem6967583 A v u f h1 h2 h3) (fun h4 : False => @lem6963840 A v u f h3)). Qed.
Lemma lem6967585 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term93 A v u f) (h2 : @FINITE A u) (h3 : term103 A v u f) : False.
Proof. exact (EQ_MP (@lem6967584 A v u f h1 h2 h3) (@lem6963840 A v u f h3)). Qed.
Lemma lem6967586 {A : Type'} (v : A -> Prop) (f : A -> nat) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : term102 A v u f.
Proof. exact (fun h0 : term103 A v u f => @lem6967585 A v u f h1 h2 h0). Qed.
Lemma lem6967587 {A : Type'} (v : A -> Prop) (f : A -> nat) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : term101 A v u f.
Proof. exact (EQ_MP (@lem6963839 A v u f) (@lem6967586 A v f u h1 h2)). Qed.
Lemma lem6967588 {A : Type'} (v : A -> Prop) (f : A -> nat) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : (term97 A v u f) = (@nsum A u f).
Proof. exact (@lem6963835 A v u f (@lem6967587 A v f u h1 h2)). Qed.
Lemma lem6967589 {A : Type'} (v : A -> Prop) (f : A -> nat) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : (term96 A u v f) = (@nsum A u f).
Proof. exact (EQ_MP (@lem6963831 A v u f) (@lem6967588 A v f u h1 h2)). Qed.
Lemma lem6967590 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term92 A v u f) : term93 A v u f.
Proof. exact (proj2 (@lem6963815 A v u f h1)). Qed.
Lemma lem6967591 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term92 A v u f) : @FINITE A u.
Proof. exact (proj1 (@lem6963815 A v u f h1)). Qed.
Lemma lem6967592 {A : Type'} (v : A -> Prop) (f : A -> nat) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : (term93 A v u f) = ((term96 A u v f) = (@nsum A u f)).
Proof. exact (prop_ext (fun h3 : term93 A v u f => @lem6967589 A v f u h1 h2) (fun h3 : (term96 A u v f) = (@nsum A u f) => @lem6963816 A v u f h1)). Qed.
Lemma lem6967593 {A : Type'} (v : A -> Prop) (f : A -> nat) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : (term96 A u v f) = (@nsum A u f).
Proof. exact (EQ_MP (@lem6967592 A v f u h1 h2) (@lem6963816 A v u f h1)). Qed.
Lemma lem6967594 {A : Type'} (v : A -> Prop) (f : A -> nat) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : (@FINITE A u) = ((term96 A u v f) = (@nsum A u f)).
Proof. exact (prop_ext (fun h3 : @FINITE A u => @lem6967593 A v f u h1 h2) (fun h3 : (term96 A u v f) = (@nsum A u f) => @lem6963817 A u h2)). Qed.
Lemma lem6967595 {A : Type'} (v : A -> Prop) (f : A -> nat) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : (term96 A u v f) = (@nsum A u f).
Proof. exact (EQ_MP (@lem6967594 A v f u h1 h2) (@lem6963817 A u h2)). Qed.
Lemma lem6967596 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : @FINITE A u) (h2 : term92 A v u f) : (term93 A v u f) = ((term96 A u v f) = (@nsum A u f)).
Proof. exact (prop_ext (fun h3 : term93 A v u f => @lem6967595 A v f u h3 h1) (fun h3 : (term96 A u v f) = (@nsum A u f) => @lem6967590 A v u f h2)). Qed.
Lemma lem6967597 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : @FINITE A u) (h2 : term92 A v u f) : (term96 A u v f) = (@nsum A u f).
Proof. exact (EQ_MP (@lem6967596 A v u f h1 h2) (@lem6967590 A v u f h2)). Qed.
Lemma lem6967598 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term92 A v u f) : (@FINITE A u) = ((term96 A u v f) = (@nsum A u f)).
Proof. exact (prop_ext (fun h2 : @FINITE A u => @lem6967597 A v u f h2 h1) (fun h2 : (term96 A u v f) = (@nsum A u f) => @lem6967591 A v u f h1)). Qed.
Lemma lem6967599 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (h1 : term92 A v u f) : (term96 A u v f) = (@nsum A u f).
Proof. exact (EQ_MP (@lem6967598 A v u f h1) (@lem6967591 A v u f h1)). Qed.
Lemma lem6967600 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : term625 A v u f.
Proof. exact (fun h0 : term92 A v u f => @lem6967599 A v u f h0). Qed.
Lemma lem6967605 {A : Type'} (u : A -> Prop) (f : A -> nat) : term626 A u f.
Proof. exact (fun v : A -> Prop => @lem6967600 A v u f). Qed.
Lemma lem6967610 {A : Type'} (f : A -> nat) : term627 A f.
Proof. exact (fun u : A -> Prop => @lem6967605 A u f). Qed.
Lemma lem6967615 {A : Type'} : term628 A.
Proof. exact (fun f : A -> nat => @lem6967610 A f). Qed.
