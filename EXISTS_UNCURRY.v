Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_UNCURRY_term_abbrevs.
Require Import FORALL_UNCURRY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem53019 {A B C : Type'} (P : type443 A B C) : term0 A B C P.
Proof. exact (@lem53018 A B C P). Qed.
Lemma lem53020 {A B C : Type'} (P : type443 A B C) : (term0 A B C P) = ((term1 A B C P) = (term2 A B C P)).
Proof. exact (eq_refl (term0 A B C P)). Qed.
Lemma lem53033 (p : Prop) : p = (term3 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem53034 {_5387 : Type'} (P : _5387 -> Prop) : ((term4 _5387 P) = (term5 _5387 P)) = (term6 _5387 P).
Proof. exact (@lem53033 ((term4 _5387 P) = (term5 _5387 P))). Qed.
Lemma lem53035 {_5387 : Type'} (P : _5387 -> Prop) : (term6 _5387 P) = ((term4 _5387 P) = (term5 _5387 P)).
Proof. exact (SYM (@lem53034 _5387 P)). Qed.
Lemma lem53036 {_5387 : Type'} (P : _5387 -> Prop) (h1 : term7 _5387 P) : term7 _5387 P.
Proof. exact (h1). Qed.
Lemma lem53039 {_5387 : Type'} (P : _5387 -> Prop) (h1 : term6 _5387 P) : term6 _5387 P.
Proof. exact (h1). Qed.
Lemma lem53040 {_5387 : Type'} (P : _5387 -> Prop) : term8 _5387 P.
Proof. exact (fun h0 : term6 _5387 P => @lem53039 _5387 P h0). Qed.
Lemma lem53041 {_5387 : Type'} (P : _5387 -> Prop) (h1 : term8 _5387 P) : term8 _5387 P.
Proof. exact (h1). Qed.
Lemma lem53042 {_5387 : Type'} (P : _5387 -> Prop) (h1 : term6 _5387 P) : term6 _5387 P.
Proof. exact (h1). Qed.
Lemma lem53043 {_5387 : Type'} (P : _5387 -> Prop) (h1 : term6 _5387 P) (h2 : term8 _5387 P) : term6 _5387 P.
Proof. exact (@lem53041 _5387 P h2 (@lem53042 _5387 P h1)). Qed.
Lemma lem53044 {_5387 : Type'} (P : _5387 -> Prop) (h1 : term6 _5387 P) : term9 _5387 P.
Proof. exact (fun h0 : term8 _5387 P => @lem53043 _5387 P h1 h0). Qed.
Lemma lem53045 {_5387 : Type'} (P : _5387 -> Prop) (h1 : term8 _5387 P) : term8 _5387 P.
Proof. exact (h1). Qed.
Lemma lem53046 {_5387 : Type'} (P : _5387 -> Prop) (h1 : term6 _5387 P) (h2 : term8 _5387 P) : term6 _5387 P.
Proof. exact (@lem53044 _5387 P h1 (@lem53045 _5387 P h2)). Qed.
Lemma lem53047 {_5387 : Type'} (P : _5387 -> Prop) (h1 : term8 _5387 P) : term8 _5387 P.
Proof. exact (fun h0 : term6 _5387 P => @lem53046 _5387 P h0 h1). Qed.
Lemma lem53048 {_5387 : Type'} (P : _5387 -> Prop) : term10 _5387 P.
Proof. exact (fun h0 : term8 _5387 P => @lem53047 _5387 P h0). Qed.
Lemma lem53051 {_5387 : Type'} (P : _5387 -> Prop) : term8 _5387 P.
Proof. exact (@lem53048 _5387 P (@lem53040 _5387 P)). Qed.
Lemma lem53052 {_5387 : Type'} (P : _5387 -> Prop) : term8 _5387 P.
Proof. exact (@lem53051 _5387 P). Qed.
Lemma lem53058 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem53059 {_5387 : Type'} (P : _5387 -> Prop) : (term6 _5387 P) = (term11 _5387 P).
Proof. exact (@lem53058 (term7 _5387 P)). Qed.
Lemma lem53061 (t : Prop) : (term12 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem53062 {_5387 : Type'} (P : _5387 -> Prop) : (term11 _5387 P) = ((term4 _5387 P) = (term5 _5387 P)).
Proof. exact (@lem53061 ((term4 _5387 P) = (term5 _5387 P))). Qed.
Lemma lem53063 {_5387 : Type'} (P : _5387 -> Prop) : (term6 _5387 P) = ((term4 _5387 P) = (term5 _5387 P)).
Proof. exact (TRANS (@lem53059 _5387 P) (@lem53062 _5387 P)). Qed.
Lemma lem53072 {_5387 : Type'} : (term13 _5387) = (term14 _5387).
Proof. exact (fun_ext (fun P : _5387 -> Prop => @lem53063 _5387 P)). Qed.
Lemma lem53073 {_5387 : Type'} : (@all (_5387 -> Prop)) = (@all (_5387 -> Prop)).
Proof. exact (eq_refl (@all (_5387 -> Prop))). Qed.
Lemma lem53082 {_5387 : Type'} : (term15 _5387) = (term16 _5387).
Proof. exact (MK_COMB (@lem53073 _5387) (@lem53072 _5387)). Qed.
Lemma lem53085 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term17 _5387 P x) = (term17 _5387 P x).
Proof. exact (eq_refl (term17 _5387 P x)). Qed.
Lemma lem53086 {_5387 : Type'} (P : _5387 -> Prop) : (term18 _5387 P) = (term18 _5387 P).
Proof. exact (fun_ext (fun x : _5387 => @lem53085 _5387 P x)). Qed.
Lemma lem53087 {_5387 : Type'} : (@all _5387) = (@all _5387).
Proof. exact (eq_refl (@all _5387)). Qed.
Lemma lem53088 {_5387 : Type'} (P : _5387 -> Prop) : (term19 _5387 P) = (term19 _5387 P).
Proof. exact (MK_COMB (@lem53087 _5387) (@lem53086 _5387 P)). Qed.
Lemma lem53089 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem53090 {_5387 : Type'} (P : _5387 -> Prop) : (term5 _5387 P) = (term5 _5387 P).
Proof. exact (MK_COMB (@lem53089) (@lem53088 _5387 P)). Qed.
Lemma lem53091 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem53092 {_5387 : Type'} (P : _5387 -> Prop) : (term20 _5387 P) = (term20 _5387 P).
Proof. exact (fun_ext (fun x : _5387 => @lem53091 _5387 P x)). Qed.
Lemma lem53093 {_5387 : Type'} : (@ex _5387) = (@ex _5387).
Proof. exact (eq_refl (@ex _5387)). Qed.
Lemma lem53094 {_5387 : Type'} (P : _5387 -> Prop) : (term4 _5387 P) = (term4 _5387 P).
Proof. exact (MK_COMB (@lem53093 _5387) (@lem53092 _5387 P)). Qed.
Lemma lem53095 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem53096 {_5387 : Type'} (P : _5387 -> Prop) : (term21 _5387 P) = (term21 _5387 P).
Proof. exact (MK_COMB (@lem53095) (@lem53094 _5387 P)). Qed.
Lemma lem53097 {_5387 : Type'} (P : _5387 -> Prop) : ((term4 _5387 P) = (term5 _5387 P)) = ((term4 _5387 P) = (term5 _5387 P)).
Proof. exact (MK_COMB (@lem53096 _5387 P) (@lem53090 _5387 P)). Qed.
Lemma lem53098 {_5387 : Type'} : (term14 _5387) = (term14 _5387).
Proof. exact (fun_ext (fun P : _5387 -> Prop => @lem53097 _5387 P)). Qed.
Lemma lem53099 {_5387 : Type'} : (@all (_5387 -> Prop)) = (@all (_5387 -> Prop)).
Proof. exact (eq_refl (@all (_5387 -> Prop))). Qed.
Lemma lem53100 {_5387 : Type'} : (term16 _5387) = (term16 _5387).
Proof. exact (MK_COMB (@lem53099 _5387) (@lem53098 _5387)). Qed.
Lemma lem53121 {_5387 : Type'} : (term15 _5387) = (term16 _5387).
Proof. exact (TRANS (@lem53082 _5387) (@lem53100 _5387)). Qed.
Lemma lem53122 {_5387 : Type'} : (term16 _5387) = (term15 _5387).
Proof. exact (SYM (@lem53121 _5387)). Qed.
Lemma lem53124 (p : Prop) : p = (term3 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem53125 {_5387 : Type'} (P : _5387 -> Prop) : ((term4 _5387 P) = (term5 _5387 P)) = (term6 _5387 P).
Proof. exact (@lem53124 ((term4 _5387 P) = (term5 _5387 P))). Qed.
Lemma lem53126 {_5387 : Type'} (P : _5387 -> Prop) : (term6 _5387 P) = ((term4 _5387 P) = (term5 _5387 P)).
Proof. exact (SYM (@lem53125 _5387 P)). Qed.
Lemma lem53127 {_5387 : Type'} (P : _5387 -> Prop) (h1 : term7 _5387 P) : term7 _5387 P.
Proof. exact (h1). Qed.
Lemma lem53129 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem53130 {_5387 : Type'} (P : _5387 -> Prop) : (term22 _5387 P) = (term19 _5387 P).
Proof. exact (@lem18394 _5387 P). Qed.
Lemma lem53131 {_5387 : Type'} (P : _5387 -> Prop) : (term23 _5387 P) = (term24 _5387 P).
Proof. exact (@lem53130 _5387 (term20 _5387 P)). Qed.
Lemma lem53132 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term25 _5387 P x) = (P x).
Proof. exact (eq_refl (term25 _5387 P x)). Qed.
Lemma lem53133 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem53135 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term26 _5387 P x) = (term17 _5387 P x).
Proof. exact (MK_COMB (@lem53133) (@lem53132 _5387 P x)). Qed.
Lemma lem53136 {_5387 : Type'} (P : _5387 -> Prop) : (term27 _5387 P) = (term18 _5387 P).
Proof. exact (fun_ext (fun x : _5387 => @lem53135 _5387 P x)). Qed.
Lemma lem53137 {_5387 : Type'} : (@all _5387) = (@all _5387).
Proof. exact (eq_refl (@all _5387)). Qed.
Lemma lem53138 {_5387 : Type'} (P : _5387 -> Prop) : (term24 _5387 P) = (term19 _5387 P).
Proof. exact (MK_COMB (@lem53137 _5387) (@lem53136 _5387 P)). Qed.
Lemma lem53139 {_5387 : Type'} (P : _5387 -> Prop) : (term23 _5387 P) = (term19 _5387 P).
Proof. exact (TRANS (@lem53131 _5387 P) (@lem53138 _5387 P)). Qed.
Lemma lem53140 {_5387 : Type'} (P : _5387 -> Prop) : (term20 _5387 P) = (term20 _5387 P).
Proof. exact (fun_ext (fun x : _5387 => @lem53129 _5387 P x)). Qed.
Lemma lem53141 {_5387 : Type'} : (@ex _5387) = (@ex _5387).
Proof. exact (eq_refl (@ex _5387)). Qed.
Lemma lem53142 {_5387 : Type'} (P : _5387 -> Prop) : (term4 _5387 P) = (term4 _5387 P).
Proof. exact (MK_COMB (@lem53141 _5387) (@lem53140 _5387 P)). Qed.
Lemma lem53143 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term17 _5387 P x) = (term17 _5387 P x).
Proof. exact (eq_refl (term17 _5387 P x)). Qed.
Lemma lem53146 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term28 _5387 P x) = (P x).
Proof. exact (@lem16933 (P x)). Qed.
Lemma lem53147 {_5387 : Type'} (P : _5387 -> Prop) : (term29 _5387 P) = (term30 _5387 P).
Proof. exact (@lem18392 _5387 P). Qed.
Lemma lem53148 {_5387 : Type'} (P : _5387 -> Prop) : (term5 _5387 P) = (term31 _5387 P).
Proof. exact (@lem53147 _5387 (term18 _5387 P)). Qed.
Lemma lem53149 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term32 _5387 P x) = (term17 _5387 P x).
Proof. exact (eq_refl (term32 _5387 P x)). Qed.
Lemma lem53150 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem53151 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term33 _5387 P x) = (term28 _5387 P x).
Proof. exact (MK_COMB (@lem53150) (@lem53149 _5387 P x)). Qed.
Lemma lem53152 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term33 _5387 P x) = (P x).
Proof. exact (TRANS (@lem53151 _5387 P x) (@lem53146 _5387 P x)). Qed.
Lemma lem53153 {_5387 : Type'} (P : _5387 -> Prop) : (term34 _5387 P) = (term20 _5387 P).
Proof. exact (fun_ext (fun x : _5387 => @lem53152 _5387 P x)). Qed.
Lemma lem53154 {_5387 : Type'} : (@ex _5387) = (@ex _5387).
Proof. exact (eq_refl (@ex _5387)). Qed.
Lemma lem53155 {_5387 : Type'} (P : _5387 -> Prop) : (term31 _5387 P) = (term4 _5387 P).
Proof. exact (MK_COMB (@lem53154 _5387) (@lem53153 _5387 P)). Qed.
Lemma lem53156 {_5387 : Type'} (P : _5387 -> Prop) : (term5 _5387 P) = (term4 _5387 P).
Proof. exact (TRANS (@lem53148 _5387 P) (@lem53155 _5387 P)). Qed.
Lemma lem53157 {_5387 : Type'} (P : _5387 -> Prop) : (term18 _5387 P) = (term18 _5387 P).
Proof. exact (fun_ext (fun x : _5387 => @lem53143 _5387 P x)). Qed.
Lemma lem53158 {_5387 : Type'} : (@all _5387) = (@all _5387).
Proof. exact (eq_refl (@all _5387)). Qed.
Lemma lem53159 {_5387 : Type'} (P : _5387 -> Prop) : (term19 _5387 P) = (term19 _5387 P).
Proof. exact (MK_COMB (@lem53158 _5387) (@lem53157 _5387 P)). Qed.
Lemma lem53160 {_5387 : Type'} (P : _5387 -> Prop) : (term35 _5387 P) = (term19 _5387 P).
Proof. exact (@lem16933 (term19 _5387 P)). Qed.
Lemma lem53161 {_5387 : Type'} (P : _5387 -> Prop) : (term35 _5387 P) = (term19 _5387 P).
Proof. exact (TRANS (@lem53160 _5387 P) (@lem53159 _5387 P)). Qed.
Lemma lem53162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem53163 {_5387 : Type'} (P : _5387 -> Prop) : (term36 _5387 P) = (term37 _5387 P).
Proof. exact (MK_COMB (@lem53162) (@lem53139 _5387 P)). Qed.
Lemma lem53164 {_5387 : Type'} (P : _5387 -> Prop) : (term38 _5387 P) = (term39 _5387 P).
Proof. exact (MK_COMB (@lem53163 _5387 P) (@lem53156 _5387 P)). Qed.
Lemma lem53165 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem53166 {_5387 : Type'} (P : _5387 -> Prop) : (term40 _5387 P) = (term40 _5387 P).
Proof. exact (MK_COMB (@lem53165) (@lem53142 _5387 P)). Qed.
Lemma lem53167 {_5387 : Type'} (P : _5387 -> Prop) : (term41 _5387 P) = (term42 _5387 P).
Proof. exact (MK_COMB (@lem53166 _5387 P) (@lem53161 _5387 P)). Qed.
Lemma lem53168 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem53169 {_5387 : Type'} (P : _5387 -> Prop) : (term43 _5387 P) = (term44 _5387 P).
Proof. exact (MK_COMB (@lem53168) (@lem53167 _5387 P)). Qed.
Lemma lem53170 {_5387 : Type'} (P : _5387 -> Prop) : (term45 _5387 P) = (term46 _5387 P).
Proof. exact (MK_COMB (@lem53169 _5387 P) (@lem53164 _5387 P)). Qed.
Lemma lem53171 {_5387 : Type'} (P : _5387 -> Prop) : (term7 _5387 P) = (term45 _5387 P).
Proof. exact (@lem17646 (term4 _5387 P) (term5 _5387 P)). Qed.
Lemma lem53172 {_5387 : Type'} (P : _5387 -> Prop) : (term7 _5387 P) = (term46 _5387 P).
Proof. exact (TRANS (@lem53171 _5387 P) (@lem53170 _5387 P)). Qed.
Lemma lem53191 {A : Type'} (P : A -> Prop) (Q : Prop) : (term47 A P Q) = (term48 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem53192 {_5387 : Type'} (P : _5387 -> Prop) (Q : Prop) : (term47 _5387 P Q) = (term48 _5387 P Q).
Proof. exact (@lem53191 _5387 P Q). Qed.
Lemma lem53193 {_5387 : Type'} (P : _5387 -> Prop) : (term42 _5387 P) = (term49 _5387 P).
Proof. exact (@lem53192 _5387 P (term19 _5387 P)). Qed.
Lemma lem53194 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem53195 {_5387 : Type'} (P : _5387 -> Prop) : (term44 _5387 P) = (term50 _5387 P).
Proof. exact (MK_COMB (@lem53194) (@lem53193 _5387 P)). Qed.
Lemma lem53197 {A : Type'} (P : Prop) (Q : A -> Prop) : (term51 A P Q) = (term52 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem53198 {_5387 : Type'} (P : Prop) (Q : _5387 -> Prop) : (term51 _5387 P Q) = (term52 _5387 P Q).
Proof. exact (@lem53197 _5387 P Q). Qed.
Lemma lem53199 {_5387 : Type'} (P : _5387 -> Prop) : (term39 _5387 P) = (term53 _5387 P).
Proof. exact (@lem53198 _5387 (term19 _5387 P) P). Qed.
Lemma lem53200 {_5387 : Type'} (P : _5387 -> Prop) : (term46 _5387 P) = (term54 _5387 P).
Proof. exact (MK_COMB (@lem53195 _5387 P) (@lem53199 _5387 P)). Qed.
Lemma lem53202 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term56 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem53203 {_5387 : Type'} (P : _5387 -> Prop) (Q : _5387 -> Prop) : (term55 _5387 P Q) = (term56 _5387 P Q).
Proof. exact (@lem53202 _5387 P Q). Qed.
Lemma lem53204 {_5387 : Type'} (P : _5387 -> Prop) : (term57 _5387 P) = (term58 _5387 P).
Proof. exact (@lem53203 _5387 (term59 _5387 P) (term60 _5387 P)). Qed.
Lemma lem53205 {_5387 : Type'} (x : _5387) (P : _5387 -> Prop) : (term61 _5387 P x) = (term62 _5387 x P).
Proof. exact (eq_refl (term61 _5387 P x)). Qed.
Lemma lem53206 {_5387 : Type'} (P : _5387 -> Prop) : (term63 _5387 P) = (term59 _5387 P).
Proof. exact (fun_ext (fun x : _5387 => @lem53205 _5387 x P)). Qed.
Lemma lem53207 {_5387 : Type'} : (@ex _5387) = (@ex _5387).
Proof. exact (eq_refl (@ex _5387)). Qed.
Lemma lem53208 {_5387 : Type'} (P : _5387 -> Prop) : (term64 _5387 P) = (term49 _5387 P).
Proof. exact (MK_COMB (@lem53207 _5387) (@lem53206 _5387 P)). Qed.
Lemma lem53209 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem53210 {_5387 : Type'} (P : _5387 -> Prop) : (term65 _5387 P) = (term50 _5387 P).
Proof. exact (MK_COMB (@lem53209) (@lem53208 _5387 P)). Qed.
Lemma lem53211 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term66 _5387 P x) = (term67 _5387 P x).
Proof. exact (eq_refl (term66 _5387 P x)). Qed.
Lemma lem53212 {_5387 : Type'} (P : _5387 -> Prop) : (term68 _5387 P) = (term60 _5387 P).
Proof. exact (fun_ext (fun x : _5387 => @lem53211 _5387 P x)). Qed.
Lemma lem53213 {_5387 : Type'} : (@ex _5387) = (@ex _5387).
Proof. exact (eq_refl (@ex _5387)). Qed.
Lemma lem53214 {_5387 : Type'} (P : _5387 -> Prop) : (term69 _5387 P) = (term53 _5387 P).
Proof. exact (MK_COMB (@lem53213 _5387) (@lem53212 _5387 P)). Qed.
Lemma lem53215 {_5387 : Type'} (P : _5387 -> Prop) : (term57 _5387 P) = (term54 _5387 P).
Proof. exact (MK_COMB (@lem53210 _5387 P) (@lem53214 _5387 P)). Qed.
Lemma lem53216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem53217 {_5387 : Type'} (P : _5387 -> Prop) : (term70 _5387 P) = (term71 _5387 P).
Proof. exact (MK_COMB (@lem53216) (@lem53215 _5387 P)). Qed.
Lemma lem53218 {_5387 : Type'} (x : _5387) (P : _5387 -> Prop) : (term61 _5387 P x) = (term62 _5387 x P).
Proof. exact (eq_refl (term61 _5387 P x)). Qed.
Lemma lem53219 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem53220 {_5387 : Type'} (x : _5387) (P : _5387 -> Prop) : (term72 _5387 P x) = (term73 _5387 x P).
Proof. exact (MK_COMB (@lem53219) (@lem53218 _5387 x P)). Qed.
Lemma lem53221 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term66 _5387 P x) = (term67 _5387 P x).
Proof. exact (eq_refl (term66 _5387 P x)). Qed.
Lemma lem53222 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term74 _5387 P x) = (term75 _5387 P x).
Proof. exact (MK_COMB (@lem53220 _5387 x P) (@lem53221 _5387 P x)). Qed.
Lemma lem53223 {_5387 : Type'} (P : _5387 -> Prop) : (term76 _5387 P) = (term77 _5387 P).
Proof. exact (fun_ext (fun x : _5387 => @lem53222 _5387 P x)). Qed.
Lemma lem53224 {_5387 : Type'} : (@ex _5387) = (@ex _5387).
Proof. exact (eq_refl (@ex _5387)). Qed.
Lemma lem53225 {_5387 : Type'} (P : _5387 -> Prop) : (term58 _5387 P) = (term78 _5387 P).
Proof. exact (MK_COMB (@lem53224 _5387) (@lem53223 _5387 P)). Qed.
Lemma lem53226 {_5387 : Type'} (P : _5387 -> Prop) : ((term57 _5387 P) = (term58 _5387 P)) = ((term54 _5387 P) = (term78 _5387 P)).
Proof. exact (MK_COMB (@lem53217 _5387 P) (@lem53225 _5387 P)). Qed.
Lemma lem53227 {_5387 : Type'} (P : _5387 -> Prop) : (term54 _5387 P) = (term78 _5387 P).
Proof. exact (EQ_MP (@lem53226 _5387 P) (@lem53204 _5387 P)). Qed.
Lemma lem53229 {_5387 : Type'} (P : _5387 -> Prop) : (term46 _5387 P) = (term78 _5387 P).
Proof. exact (TRANS (@lem53200 _5387 P) (@lem53227 _5387 P)). Qed.
Lemma lem53230 {_5387 : Type'} (P : _5387 -> Prop) : (term7 _5387 P) = (term78 _5387 P).
Proof. exact (TRANS (@lem53172 _5387 P) (@lem53229 _5387 P)). Qed.
Lemma lem53231 {_5387 : Type'} (P : _5387 -> Prop) (h1 : term7 _5387 P) : term78 _5387 P.
Proof. exact (EQ_MP (@lem53230 _5387 P) (@lem53127 _5387 P h1)). Qed.
Lemma lem53232 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) (h1 : term75 _5387 P x) : term75 _5387 P x.
Proof. exact (h1). Qed.
Lemma lem53235 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem53240 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term17 _5387 P x) = (term17 _5387 P x).
Proof. exact (eq_refl (term17 _5387 P x)). Qed.
Lemma lem53241 {_5387 : Type'} (P : _5387 -> Prop) : (term18 _5387 P) = (term18 _5387 P).
Proof. exact (fun_ext (fun x : _5387 => @lem53240 _5387 P x)). Qed.
Lemma lem53242 {_5387 : Type'} : (@all _5387) = (@all _5387).
Proof. exact (eq_refl (@all _5387)). Qed.
Lemma lem53243 {_5387 : Type'} (P : _5387 -> Prop) : (term19 _5387 P) = (term19 _5387 P).
Proof. exact (MK_COMB (@lem53242 _5387) (@lem53241 _5387 P)). Qed.
Lemma lem53244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem53245 {_5387 : Type'} (P : _5387 -> Prop) : (term37 _5387 P) = (term37 _5387 P).
Proof. exact (MK_COMB (@lem53244) (@lem53243 _5387 P)). Qed.
Lemma lem53246 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term67 _5387 P x) = (term67 _5387 P x).
Proof. exact (MK_COMB (@lem53245 _5387 P) (@lem53235 _5387 P x)). Qed.
Lemma lem53251 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term17 _5387 P x) = (term17 _5387 P x).
Proof. exact (eq_refl (term17 _5387 P x)). Qed.
Lemma lem53252 {_5387 : Type'} (P : _5387 -> Prop) : (term18 _5387 P) = (term18 _5387 P).
Proof. exact (fun_ext (fun x : _5387 => @lem53251 _5387 P x)). Qed.
Lemma lem53253 {_5387 : Type'} : (@all _5387) = (@all _5387).
Proof. exact (eq_refl (@all _5387)). Qed.
Lemma lem53254 {_5387 : Type'} (P : _5387 -> Prop) : (term19 _5387 P) = (term19 _5387 P).
Proof. exact (MK_COMB (@lem53253 _5387) (@lem53252 _5387 P)). Qed.
Lemma lem53259 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term79 _5387 P x) = (term79 _5387 P x).
Proof. exact (eq_refl (term79 _5387 P x)). Qed.
Lemma lem53260 {_5387 : Type'} (x : _5387) (P : _5387 -> Prop) : (term62 _5387 x P) = (term62 _5387 x P).
Proof. exact (MK_COMB (@lem53259 _5387 P x) (@lem53254 _5387 P)). Qed.
Lemma lem53261 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem53262 {_5387 : Type'} (x : _5387) (P : _5387 -> Prop) : (term73 _5387 x P) = (term73 _5387 x P).
Proof. exact (MK_COMB (@lem53261) (@lem53260 _5387 x P)). Qed.
Lemma lem53263 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term75 _5387 P x) = (term75 _5387 P x).
Proof. exact (MK_COMB (@lem53262 _5387 x P) (@lem53246 _5387 P x)). Qed.
Lemma lem53264 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) (h1 : term75 _5387 P x) : term75 _5387 P x.
Proof. exact (EQ_MP (@lem53263 _5387 P x) (@lem53232 _5387 P x h1)). Qed.
Lemma lem53265 {_5387 : Type'} (x : _5387) (P : _5387 -> Prop) (h1 : term62 _5387 x P) : term62 _5387 x P.
Proof. exact (h1). Qed.
Lemma lem53266 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) (h1 : term67 _5387 P x) : term67 _5387 P x.
Proof. exact (h1). Qed.
Lemma lem53267 {_5387 : Type'} (x : _5387) (P : _5387 -> Prop) (h1 : term62 _5387 x P) : term19 _5387 P.
Proof. exact (proj2 (@lem53265 _5387 x P h1)). Qed.
Lemma lem53270 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) (h1 : term67 _5387 P x) : term19 _5387 P.
Proof. exact (proj1 (@lem53266 _5387 P x h1)). Qed.
Lemma lem53276 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term17 _5387 P x) = (term17 _5387 P x).
Proof. exact (eq_refl (term17 _5387 P x)). Qed.
Lemma lem53277 {_5387 : Type'} (P : _5387 -> Prop) : (term18 _5387 P) = (term18 _5387 P).
Proof. exact (fun_ext (fun x : _5387 => @lem53276 _5387 P x)). Qed.
Lemma lem53278 {_5387 : Type'} : (@all _5387) = (@all _5387).
Proof. exact (eq_refl (@all _5387)). Qed.
Lemma lem53280 {_5387 : Type'} (P : _5387 -> Prop) : (term19 _5387 P) = (term19 _5387 P).
Proof. exact (MK_COMB (@lem53278 _5387) (@lem53277 _5387 P)). Qed.
Lemma lem53281 {_5387 : Type'} (x : _5387) (P : _5387 -> Prop) (h1 : term62 _5387 x P) : term19 _5387 P.
Proof. exact (EQ_MP (@lem53280 _5387 P) (@lem53267 _5387 x P h1)). Qed.
Lemma lem53283 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term17 _5387 P x) = (term17 _5387 P x).
Proof. exact (eq_refl (term17 _5387 P x)). Qed.
Lemma lem53284 {_5387 : Type'} (P : _5387 -> Prop) : (term18 _5387 P) = (term18 _5387 P).
Proof. exact (fun_ext (fun x : _5387 => @lem53283 _5387 P x)). Qed.
Lemma lem53285 {_5387 : Type'} : (@all _5387) = (@all _5387).
Proof. exact (eq_refl (@all _5387)). Qed.
Lemma lem53287 {_5387 : Type'} (P : _5387 -> Prop) : (term19 _5387 P) = (term19 _5387 P).
Proof. exact (MK_COMB (@lem53285 _5387) (@lem53284 _5387 P)). Qed.
Lemma lem53288 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) (h1 : term67 _5387 P x) : term19 _5387 P.
Proof. exact (EQ_MP (@lem53287 _5387 P) (@lem53270 _5387 P x h1)). Qed.
Lemma lem53293 {_5387 : Type'} (_1502 : _5387) (x : _5387) (P : _5387 -> Prop) (h1 : term62 _5387 x P) : term32 _5387 P _1502.
Proof. exact (@lem53281 _5387 x P h1 _1502). Qed.
Lemma lem53294 {_5387 : Type'} (P : _5387 -> Prop) (_1502 : _5387) : (term32 _5387 P _1502) = (term17 _5387 P _1502).
Proof. exact (eq_refl (term32 _5387 P _1502)). Qed.
Lemma lem53296 {_5387 : Type'} (_1503 : _5387) (P : _5387 -> Prop) (x : _5387) (h1 : term67 _5387 P x) : term32 _5387 P _1503.
Proof. exact (@lem53288 _5387 P x h1 _1503). Qed.
Lemma lem53297 {_5387 : Type'} (P : _5387 -> Prop) (_1503 : _5387) : (term32 _5387 P _1503) = (term17 _5387 P _1503).
Proof. exact (eq_refl (term32 _5387 P _1503)). Qed.
Lemma lem53302 {_5387 : Type'} (_1502 : _5387) (x : _5387) (P : _5387 -> Prop) (h1 : term62 _5387 x P) : term17 _5387 P _1502.
Proof. exact (EQ_MP (@lem53294 _5387 P _1502) (@lem53293 _5387 _1502 x P h1)). Qed.
Lemma lem53304 {_5387 : Type'} (_1503 : _5387) (P : _5387 -> Prop) (x : _5387) (h1 : term67 _5387 P x) : term17 _5387 P _1503.
Proof. exact (EQ_MP (@lem53297 _5387 P _1503) (@lem53296 _5387 _1503 P x h1)). Qed.
Lemma lem53308 {_5387 : Type'} (x : _5387) (P : _5387 -> Prop) (h1 : term62 _5387 x P) : P x.
Proof. exact (proj1 (@lem53265 _5387 x P h1)). Qed.
Lemma lem53309 {_5387 : Type'} (x : _5387) (P : _5387 -> Prop) (h1 : term62 _5387 x P) : term80 _5387 P x.
Proof. exact (fun h0 : term17 _5387 P x => @lem53308 _5387 x P h1). Qed.
Lemma lem53311 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem53312 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term80 _5387 P x) = (P x).
Proof. exact (@lem53311 (P x)). Qed.
Lemma lem53313 {_5387 : Type'} (x : _5387) (P : _5387 -> Prop) (h1 : term62 _5387 x P) : P x.
Proof. exact (EQ_MP (@lem53312 _5387 P x) (@lem53309 _5387 x P h1)). Qed.
Lemma lem53316 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem53318 {_5387 : Type'} (P : _5387 -> Prop) (_1502 : _5387) : (term17 _5387 P _1502) = (term82 _5387 P _1502).
Proof. exact (@lem53316 (P _1502)). Qed.
Lemma lem53321 {_5387 : Type'} (_1502 : _5387) (x : _5387) (P : _5387 -> Prop) (h1 : term62 _5387 x P) : term82 _5387 P _1502.
Proof. exact (EQ_MP (@lem53318 _5387 P _1502) (@lem53302 _5387 _1502 x P h1)). Qed.
Lemma lem53322 {_5387 : Type'} (_1502 : _5387) (x : _5387) (P : _5387 -> Prop) (h1 : term62 _5387 x P) : term82 _5387 P _1502.
Proof. exact (@lem53321 _5387 _1502 x P h1). Qed.
Lemma lem53323 {_5387 : Type'} (x : _5387) (P : _5387 -> Prop) (h1 : term62 _5387 x P) : term82 _5387 P x.
Proof. exact (@lem53322 _5387 x x P h1). Qed.
Lemma lem53326 {_5387 : Type'} (x : _5387) (P : _5387 -> Prop) (h1 : term62 _5387 x P) : False.
Proof. exact (@lem53323 _5387 x P h1 (@lem53313 _5387 x P h1)). Qed.
Lemma lem53327 {_5387 : Type'} (x : _5387) (P : _5387 -> Prop) (h1 : term62 _5387 x P) : term83.
Proof. exact (fun h0 : ~ False => @lem53326 _5387 x P h1). Qed.
Lemma lem53329 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem53330 : term83 = False.
Proof. exact (@lem53329 False). Qed.
Lemma lem53331 {_5387 : Type'} (x : _5387) (P : _5387 -> Prop) (h1 : term62 _5387 x P) : False.
Proof. exact (EQ_MP (@lem53330) (@lem53327 _5387 x P h1)). Qed.
Lemma lem53333 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) (h1 : term67 _5387 P x) : P x.
Proof. exact (proj2 (@lem53266 _5387 P x h1)). Qed.
Lemma lem53334 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) (h1 : term67 _5387 P x) : term80 _5387 P x.
Proof. exact (fun h0 : term17 _5387 P x => @lem53333 _5387 P x h1). Qed.
Lemma lem53336 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem53337 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) : (term80 _5387 P x) = (P x).
Proof. exact (@lem53336 (P x)). Qed.
Lemma lem53338 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) (h1 : term67 _5387 P x) : P x.
Proof. exact (EQ_MP (@lem53337 _5387 P x) (@lem53334 _5387 P x h1)). Qed.
Lemma lem53341 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem53343 {_5387 : Type'} (P : _5387 -> Prop) (_1503 : _5387) : (term17 _5387 P _1503) = (term82 _5387 P _1503).
Proof. exact (@lem53341 (P _1503)). Qed.
Lemma lem53346 {_5387 : Type'} (_1503 : _5387) (P : _5387 -> Prop) (x : _5387) (h1 : term67 _5387 P x) : term82 _5387 P _1503.
Proof. exact (EQ_MP (@lem53343 _5387 P _1503) (@lem53304 _5387 _1503 P x h1)). Qed.
Lemma lem53347 {_5387 : Type'} (_1503 : _5387) (P : _5387 -> Prop) (x : _5387) (h1 : term67 _5387 P x) : term82 _5387 P _1503.
Proof. exact (@lem53346 _5387 _1503 P x h1). Qed.
Lemma lem53348 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) (h1 : term67 _5387 P x) : term82 _5387 P x.
Proof. exact (@lem53347 _5387 x P x h1). Qed.
Lemma lem53351 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) (h1 : term67 _5387 P x) : False.
Proof. exact (@lem53348 _5387 P x h1 (@lem53338 _5387 P x h1)). Qed.
Lemma lem53352 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) (h1 : term67 _5387 P x) : term83.
Proof. exact (fun h0 : ~ False => @lem53351 _5387 P x h1). Qed.
Lemma lem53354 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem53355 : term83 = False.
Proof. exact (@lem53354 False). Qed.
Lemma lem53356 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) (h1 : term67 _5387 P x) : False.
Proof. exact (EQ_MP (@lem53355) (@lem53352 _5387 P x h1)). Qed.
Lemma lem53357 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) (h1 : term75 _5387 P x) : False.
Proof. exact (or_elim (@lem53264 _5387 P x h1) (fun h0 : term62 _5387 x P => @lem53331 _5387 x P h0) (fun h0 : term67 _5387 P x => @lem53356 _5387 P x h0)). Qed.
Lemma lem53358 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) (h1 : term75 _5387 P x) : (term75 _5387 P x) = False.
Proof. exact (prop_ext (fun h2 : term75 _5387 P x => @lem53357 _5387 P x h1) (fun h2 : False => @lem53264 _5387 P x h1)). Qed.
Lemma lem53359 {_5387 : Type'} (P : _5387 -> Prop) (x : _5387) (h1 : term75 _5387 P x) : False.
Proof. exact (EQ_MP (@lem53358 _5387 P x h1) (@lem53264 _5387 P x h1)). Qed.
Lemma lem53360 {_5387 : Type'} (P : _5387 -> Prop) (h1 : term7 _5387 P) : False.
Proof. exact (ex_elim (@lem53231 _5387 P h1) (fun x : _5387 => fun h0 : term77 _5387 P x => @lem53359 _5387 P x h0)). Qed.
Lemma lem53361 {_5387 : Type'} (P : _5387 -> Prop) (h1 : term7 _5387 P) : (term7 _5387 P) = False.
Proof. exact (prop_ext (fun h2 : term7 _5387 P => @lem53360 _5387 P h1) (fun h2 : False => @lem53127 _5387 P h1)). Qed.
Lemma lem53362 {_5387 : Type'} (P : _5387 -> Prop) (h1 : term7 _5387 P) : False.
Proof. exact (EQ_MP (@lem53361 _5387 P h1) (@lem53127 _5387 P h1)). Qed.
Lemma lem53363 {_5387 : Type'} (P : _5387 -> Prop) : term6 _5387 P.
Proof. exact (fun h0 : term7 _5387 P => @lem53362 _5387 P h0). Qed.
Lemma lem53364 {_5387 : Type'} (P : _5387 -> Prop) : (term4 _5387 P) = (term5 _5387 P).
Proof. exact (EQ_MP (@lem53126 _5387 P) (@lem53363 _5387 P)). Qed.
Lemma lem53369 {_5387 : Type'} : term16 _5387.
Proof. exact (fun P : _5387 -> Prop => @lem53364 _5387 P). Qed.
Lemma lem53370 {_5387 : Type'} : term15 _5387.
Proof. exact (EQ_MP (@lem53122 _5387) (@lem53369 _5387)). Qed.
Lemma lem53371 {_5387 : Type'} (P : _5387 -> Prop) : term84 _5387 P.
Proof. exact (@lem53370 _5387 P). Qed.
Lemma lem53372 {_5387 : Type'} (P : _5387 -> Prop) : (term84 _5387 P) = (term6 _5387 P).
Proof. exact (eq_refl (term84 _5387 P)). Qed.
Lemma lem53373 {_5387 : Type'} (P : _5387 -> Prop) : term6 _5387 P.
Proof. exact (EQ_MP (@lem53372 _5387 P) (@lem53371 _5387 P)). Qed.
Lemma lem53375 {_5387 : Type'} (P : _5387 -> Prop) : term6 _5387 P.
Proof. exact (@lem53052 _5387 P (@lem53373 _5387 P)). Qed.
Lemma lem53376 {_5387 : Type'} (P : _5387 -> Prop) (h1 : term7 _5387 P) : False.
Proof. exact (@lem53375 _5387 P (@lem53036 _5387 P h1)). Qed.
Lemma lem53377 {_5387 : Type'} (P : _5387 -> Prop) (h1 : term7 _5387 P) : (term7 _5387 P) = False.
Proof. exact (prop_ext (fun h2 : term7 _5387 P => @lem53376 _5387 P h1) (fun h2 : False => @lem53036 _5387 P h1)). Qed.
Lemma lem53378 {_5387 : Type'} (P : _5387 -> Prop) (h1 : term7 _5387 P) : False.
Proof. exact (EQ_MP (@lem53377 _5387 P h1) (@lem53036 _5387 P h1)). Qed.
Lemma lem53379 {_5387 : Type'} (P : _5387 -> Prop) : term6 _5387 P.
Proof. exact (fun h0 : term7 _5387 P => @lem53378 _5387 P h0). Qed.
Lemma lem53392 {_5387 : Type'} (P : _5387 -> Prop) : (term4 _5387 P) = (term5 _5387 P).
Proof. exact (EQ_MP (@lem53035 _5387 P) (@lem53379 _5387 P)). Qed.
Lemma lem53393 {A B C : Type'} (P : type443 A B C) : (term85 A B C P) = (term86 A B C P).
Proof. exact (@lem53392 (type1412 A B C) P). Qed.
Lemma lem53394 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem53395 {A B C : Type'} (P : type443 A B C) : (term87 A B C P) = (term88 A B C P).
Proof. exact (MK_COMB (@lem53394) (@lem53393 A B C P)). Qed.
Lemma lem53401 {_5387 : Type'} (P : _5387 -> Prop) : (term4 _5387 P) = (term5 _5387 P).
Proof. exact (EQ_MP (@lem53035 _5387 P) (@lem53379 _5387 P)). Qed.
Lemma lem53402 {A B C : Type'} (P : type322 A B C) : (term89 A B C P) = (term90 A B C P).
Proof. exact (@lem53401 (type1209 A B C) P). Qed.
Lemma lem53403 {A B C : Type'} (P : type443 A B C) : (term91 A B C P) = (term92 A B C P).
Proof. exact (@lem53402 A B C (term93 A B C P)). Qed.
Lemma lem53404 {A B C : Type'} (P : type443 A B C) (f : type1209 A B C) : (term94 A B C P f) = (term95 A B C P f).
Proof. exact (eq_refl (term94 A B C P f)). Qed.
Lemma lem53405 {A B C : Type'} (P : type443 A B C) : (term96 A B C P) = (term93 A B C P).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem53404 A B C P f)). Qed.
Lemma lem53406 {A B C : Type'} : (@ex ((prod A B) -> C)) = (@ex ((prod A B) -> C)).
Proof. exact (eq_refl (@ex ((prod A B) -> C))). Qed.
Lemma lem53407 {A B C : Type'} (P : type443 A B C) : (term91 A B C P) = (term97 A B C P).
Proof. exact (MK_COMB (@lem53406 A B C) (@lem53405 A B C P)). Qed.
Lemma lem53408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem53409 {A B C : Type'} (P : type443 A B C) : (term98 A B C P) = (term99 A B C P).
Proof. exact (MK_COMB (@lem53408) (@lem53407 A B C P)). Qed.
Lemma lem53410 {A B C : Type'} (P : type443 A B C) (f : type1209 A B C) : (term94 A B C P f) = (term95 A B C P f).
Proof. exact (eq_refl (term94 A B C P f)). Qed.
Lemma lem53411 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem53412 {A B C : Type'} (P : type443 A B C) (f : type1209 A B C) : (term100 A B C P f) = (term101 A B C P f).
Proof. exact (MK_COMB (@lem53411) (@lem53410 A B C P f)). Qed.
Lemma lem53413 {A B C : Type'} (P : type443 A B C) : (term102 A B C P) = (term103 A B C P).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem53412 A B C P f)). Qed.
Lemma lem53414 {A B C : Type'} : (@all ((prod A B) -> C)) = (@all ((prod A B) -> C)).
Proof. exact (eq_refl (@all ((prod A B) -> C))). Qed.
Lemma lem53415 {A B C : Type'} (P : type443 A B C) : (term104 A B C P) = (term105 A B C P).
Proof. exact (MK_COMB (@lem53414 A B C) (@lem53413 A B C P)). Qed.
Lemma lem53416 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem53417 {A B C : Type'} (P : type443 A B C) : (term92 A B C P) = (term106 A B C P).
Proof. exact (MK_COMB (@lem53416) (@lem53415 A B C P)). Qed.
Lemma lem53418 {A B C : Type'} (P : type443 A B C) : ((term91 A B C P) = (term92 A B C P)) = ((term97 A B C P) = (term106 A B C P)).
Proof. exact (MK_COMB (@lem53409 A B C P) (@lem53417 A B C P)). Qed.
Lemma lem53419 {A B C : Type'} (P : type443 A B C) : (term97 A B C P) = (term106 A B C P).
Proof. exact (EQ_MP (@lem53418 A B C P) (@lem53403 A B C P)). Qed.
Lemma lem53420 {A B C : Type'} (P : type443 A B C) : ((term85 A B C P) = (term97 A B C P)) = ((term86 A B C P) = (term106 A B C P)).
Proof. exact (MK_COMB (@lem53395 A B C P) (@lem53419 A B C P)). Qed.
Lemma lem53421 {A B C : Type'} : (term107 A B C) = (term108 A B C).
Proof. exact (fun_ext (fun P : type443 A B C => @lem53420 A B C P)). Qed.
Lemma lem53422 {A B C : Type'} : (@all ((A -> B -> C) -> Prop)) = (@all ((A -> B -> C) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B -> C) -> Prop))). Qed.
Lemma lem53423 {A B C : Type'} : (term109 A B C) = (term110 A B C).
Proof. exact (MK_COMB (@lem53422 A B C) (@lem53421 A B C)). Qed.
Lemma lem53424 {A B C : Type'} : (term110 A B C) = (term109 A B C).
Proof. exact (SYM (@lem53423 A B C)). Qed.
Lemma lem53438 {A B C : Type'} (P : type443 A B C) : (term1 A B C P) = (term2 A B C P).
Proof. exact (EQ_MP (@lem53020 A B C P) (@lem53019 A B C P)). Qed.
Lemma lem53439 {A B C : Type'} (P : type443 A B C) : (term1 A B C P) = (term2 A B C P).
Proof. exact (@lem53438 A B C P). Qed.
Lemma lem53440 {A B C : Type'} (P : type443 A B C) : (term111 A B C P) = (term112 A B C P).
Proof. exact (@lem53439 A B C (term113 A B C P)). Qed.
Lemma lem53441 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) : (term114 A B C P f) = (term115 A B C P f).
Proof. exact (eq_refl (term114 A B C P f)). Qed.
Lemma lem53442 {A B C : Type'} (P : type443 A B C) : (term116 A B C P) = (term113 A B C P).
Proof. exact (fun_ext (fun f : type1412 A B C => @lem53441 A B C P f)). Qed.
Lemma lem53443 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem53444 {A B C : Type'} (P : type443 A B C) : (term111 A B C P) = (term117 A B C P).
Proof. exact (MK_COMB (@lem53443 A B C) (@lem53442 A B C P)). Qed.
Lemma lem53445 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem53446 {A B C : Type'} (P : type443 A B C) : (term118 A B C P) = (term119 A B C P).
Proof. exact (MK_COMB (@lem53445) (@lem53444 A B C P)). Qed.
Lemma lem53447 {A B C : Type'} (P : type443 A B C) (f : type1209 A B C) : (term120 A B C P f) = (term101 A B C P f).
Proof. exact (eq_refl (term120 A B C P f)). Qed.
Lemma lem53448 {A B C : Type'} (P : type443 A B C) : (term121 A B C P) = (term103 A B C P).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem53447 A B C P f)). Qed.
Lemma lem53449 {A B C : Type'} : (@all ((prod A B) -> C)) = (@all ((prod A B) -> C)).
Proof. exact (eq_refl (@all ((prod A B) -> C))). Qed.
Lemma lem53450 {A B C : Type'} (P : type443 A B C) : (term112 A B C P) = (term105 A B C P).
Proof. exact (MK_COMB (@lem53449 A B C) (@lem53448 A B C P)). Qed.
Lemma lem53451 {A B C : Type'} (P : type443 A B C) : ((term111 A B C P) = (term112 A B C P)) = ((term117 A B C P) = (term105 A B C P)).
Proof. exact (MK_COMB (@lem53446 A B C P) (@lem53450 A B C P)). Qed.
Lemma lem53452 {A B C : Type'} (P : type443 A B C) : (term117 A B C P) = (term105 A B C P).
Proof. exact (EQ_MP (@lem53451 A B C P) (@lem53440 A B C P)). Qed.
Lemma lem53459 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem53460 {A B C : Type'} (P : type443 A B C) : (term86 A B C P) = (term106 A B C P).
Proof. exact (MK_COMB (@lem53459) (@lem53452 A B C P)). Qed.
Lemma lem53461 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem53462 {A B C : Type'} (P : type443 A B C) : (term88 A B C P) = (term122 A B C P).
Proof. exact (MK_COMB (@lem53461) (@lem53460 A B C P)). Qed.
Lemma lem53469 {A B C : Type'} (P : type443 A B C) : (term106 A B C P) = (term106 A B C P).
Proof. exact (eq_refl (term106 A B C P)). Qed.
Lemma lem53470 {A B C : Type'} (P : type443 A B C) : ((term86 A B C P) = (term106 A B C P)) = ((term106 A B C P) = (term106 A B C P)).
Proof. exact (MK_COMB (@lem53462 A B C P) (@lem53469 A B C P)). Qed.
Lemma lem53472 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem53473 (x : Prop) : (x = x) = True.
Proof. exact (@lem53472 Prop x). Qed.
Lemma lem53474 {A B C : Type'} (P : type443 A B C) : ((term106 A B C P) = (term106 A B C P)) = True.
Proof. exact (@lem53473 (term106 A B C P)). Qed.
Lemma lem53475 {A B C : Type'} (P : type443 A B C) : ((term86 A B C P) = (term106 A B C P)) = True.
Proof. exact (TRANS (@lem53470 A B C P) (@lem53474 A B C P)). Qed.
Lemma lem53476 {A B C : Type'} : (term108 A B C) = (term123 A B C).
Proof. exact (fun_ext (fun P : type443 A B C => @lem53475 A B C P)). Qed.
Lemma lem53477 {A B C : Type'} : (@all ((A -> B -> C) -> Prop)) = (@all ((A -> B -> C) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B -> C) -> Prop))). Qed.
Lemma lem53478 {A B C : Type'} : (term110 A B C) = (term124 A B C).
Proof. exact (MK_COMB (@lem53477 A B C) (@lem53476 A B C)). Qed.
Lemma lem53480 {A : Type'} (t : Prop) : (term125 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem53481 {A B C : Type'} (t : Prop) : (term126 A B C t) = t.
Proof. exact (@lem53480 (type443 A B C) t). Qed.
Lemma lem53482 {A B C : Type'} : (term124 A B C) = True.
Proof. exact (@lem53481 A B C True). Qed.
Lemma lem53483 {A B C : Type'} : (term110 A B C) = True.
Proof. exact (TRANS (@lem53478 A B C) (@lem53482 A B C)). Qed.
Lemma lem53484 {A B C : Type'} : True = (term110 A B C).
Proof. exact (SYM (@lem53483 A B C)). Qed.
Lemma lem53485 {A B C : Type'} : term110 A B C.
Proof. exact (EQ_MP (@lem53484 A B C) (@lem0)). Qed.
Lemma lem53486 {A B C : Type'} : term109 A B C.
Proof. exact (EQ_MP (@lem53424 A B C) (@lem53485 A B C)). Qed.
