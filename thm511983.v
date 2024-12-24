Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm511983_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem510984 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term0 _17370 _17371 P Q) : term0 _17370 _17371 P Q.
Proof. exact (h1). Qed.
Lemma lem510987 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term1 _17370 _17371 P Q) : term1 _17370 _17371 P Q.
Proof. exact (h1). Qed.
Lemma lem510988 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : term2 _17370 _17371 P Q.
Proof. exact (fun h0 : term1 _17370 _17371 P Q => @lem510987 _17370 _17371 P Q h0). Qed.
Lemma lem510989 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term2 _17370 _17371 P Q) : term2 _17370 _17371 P Q.
Proof. exact (h1). Qed.
Lemma lem510990 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term1 _17370 _17371 P Q) : term1 _17370 _17371 P Q.
Proof. exact (h1). Qed.
Lemma lem510991 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term1 _17370 _17371 P Q) (h2 : term2 _17370 _17371 P Q) : term1 _17370 _17371 P Q.
Proof. exact (@lem510989 _17370 _17371 P Q h2 (@lem510990 _17370 _17371 P Q h1)). Qed.
Lemma lem510992 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term1 _17370 _17371 P Q) : term3 _17370 _17371 P Q.
Proof. exact (fun h0 : term2 _17370 _17371 P Q => @lem510991 _17370 _17371 P Q h1 h0). Qed.
Lemma lem510993 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term2 _17370 _17371 P Q) : term2 _17370 _17371 P Q.
Proof. exact (h1). Qed.
Lemma lem510994 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term1 _17370 _17371 P Q) (h2 : term2 _17370 _17371 P Q) : term1 _17370 _17371 P Q.
Proof. exact (@lem510992 _17370 _17371 P Q h1 (@lem510993 _17370 _17371 P Q h2)). Qed.
Lemma lem510995 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term2 _17370 _17371 P Q) : term2 _17370 _17371 P Q.
Proof. exact (fun h0 : term1 _17370 _17371 P Q => @lem510994 _17370 _17371 P Q h0 h1). Qed.
Lemma lem510996 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : term4 _17370 _17371 P Q.
Proof. exact (fun h0 : term2 _17370 _17371 P Q => @lem510995 _17370 _17371 P Q h0). Qed.
Lemma lem510999 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : term2 _17370 _17371 P Q.
Proof. exact (@lem510996 _17370 _17371 P Q (@lem510988 _17370 _17371 P Q)). Qed.
Lemma lem511000 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : term2 _17370 _17371 P Q.
Proof. exact (@lem510999 _17370 _17371 P Q). Qed.
Lemma lem511010 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem511011 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term1 _17370 _17371 P Q) = (term5 _17370 _17371 P Q).
Proof. exact (@lem511010 (term0 _17370 _17371 P Q)). Qed.
Lemma lem511013 (t : Prop) : (term6 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem511014 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term5 _17370 _17371 P Q) = ((term7 _17370 _17371 P Q) = (term8 _17370 _17371 P Q)).
Proof. exact (@lem511013 ((term7 _17370 _17371 P Q) = (term8 _17370 _17371 P Q))). Qed.
Lemma lem511015 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term1 _17370 _17371 P Q) = ((term7 _17370 _17371 P Q) = (term8 _17370 _17371 P Q)).
Proof. exact (TRANS (@lem511011 _17370 _17371 P Q) (@lem511014 _17370 _17371 P Q)). Qed.
Lemma lem511036 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) : (term9 _17370 _17371 Q) = (term10 _17370 _17371 Q).
Proof. exact (fun_ext (fun P : _17371 -> Prop => @lem511015 _17370 _17371 P Q)). Qed.
Lemma lem511037 {_17371 : Type'} : (@all (_17371 -> Prop)) = (@all (_17371 -> Prop)).
Proof. exact (eq_refl (@all (_17371 -> Prop))). Qed.
Lemma lem511038 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) : (term11 _17370 _17371 Q) = (term12 _17370 _17371 Q).
Proof. exact (MK_COMB (@lem511037 _17371) (@lem511036 _17370 _17371 Q)). Qed.
Lemma lem511043 {_17370 _17371 : Type'} : (term13 _17370 _17371) = (term14 _17370 _17371).
Proof. exact (fun_ext (fun Q : type1470 _17370 _17371 => @lem511038 _17370 _17371 Q)). Qed.
Lemma lem511044 {_17370 _17371 : Type'} : (@all (_17371 -> _17370 -> Prop)) = (@all (_17371 -> _17370 -> Prop)).
Proof. exact (eq_refl (@all (_17371 -> _17370 -> Prop))). Qed.
Lemma lem511053 {_17370 _17371 : Type'} : (term15 _17370 _17371) = (term16 _17370 _17371).
Proof. exact (MK_COMB (@lem511044 _17370 _17371) (@lem511043 _17370 _17371)). Qed.
Lemma lem511058 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term17 _17370 _17371 P Q x y) = (term17 _17370 _17371 P Q x y).
Proof. exact (eq_refl (term17 _17370 _17371 P Q x y)). Qed.
Lemma lem511059 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term18 _17370 _17371 P Q y) = (term18 _17370 _17371 P Q y).
Proof. exact (fun_ext (fun x : _17371 => @lem511058 _17370 _17371 P Q x y)). Qed.
Lemma lem511060 {_17371 : Type'} : (@all _17371) = (@all _17371).
Proof. exact (eq_refl (@all _17371)). Qed.
Lemma lem511061 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term19 _17370 _17371 P Q y) = (term19 _17370 _17371 P Q y).
Proof. exact (MK_COMB (@lem511060 _17371) (@lem511059 _17370 _17371 P Q y)). Qed.
Lemma lem511062 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term20 _17370 _17371 P Q) = (term20 _17370 _17371 P Q).
Proof. exact (fun_ext (fun y : _17370 => @lem511061 _17370 _17371 P Q y)). Qed.
Lemma lem511063 {_17370 : Type'} : (@all _17370) = (@all _17370).
Proof. exact (eq_refl (@all _17370)). Qed.
Lemma lem511064 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term8 _17370 _17371 P Q) = (term8 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511063 _17370) (@lem511062 _17370 _17371 P Q)). Qed.
Lemma lem511065 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (Q x y) = (Q x y).
Proof. exact (eq_refl (Q x y)). Qed.
Lemma lem511066 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) : (term21 _17370 _17371 Q x) = (term21 _17370 _17371 Q x).
Proof. exact (fun_ext (fun y : _17370 => @lem511065 _17370 _17371 Q x y)). Qed.
Lemma lem511067 {_17370 : Type'} : (@all _17370) = (@all _17370).
Proof. exact (eq_refl (@all _17370)). Qed.
Lemma lem511068 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) : (term22 _17370 _17371 Q x) = (term22 _17370 _17371 Q x).
Proof. exact (MK_COMB (@lem511067 _17370) (@lem511066 _17370 _17371 Q x)). Qed.
Lemma lem511071 {_17371 : Type'} (P : _17371 -> Prop) (x : _17371) : (term23 _17371 P x) = (term23 _17371 P x).
Proof. exact (eq_refl (term23 _17371 P x)). Qed.
Lemma lem511072 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term24 _17370 _17371 P Q x) = (term24 _17370 _17371 P Q x).
Proof. exact (MK_COMB (@lem511071 _17371 P x) (@lem511068 _17370 _17371 Q x)). Qed.
Lemma lem511073 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term25 _17370 _17371 P Q) = (term25 _17370 _17371 P Q).
Proof. exact (fun_ext (fun x : _17371 => @lem511072 _17370 _17371 P Q x)). Qed.
Lemma lem511074 {_17371 : Type'} : (@all _17371) = (@all _17371).
Proof. exact (eq_refl (@all _17371)). Qed.
Lemma lem511075 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term7 _17370 _17371 P Q) = (term7 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511074 _17371) (@lem511073 _17370 _17371 P Q)). Qed.
Lemma lem511076 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem511077 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term26 _17370 _17371 P Q) = (term26 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511076) (@lem511075 _17370 _17371 P Q)). Qed.
Lemma lem511078 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : ((term7 _17370 _17371 P Q) = (term8 _17370 _17371 P Q)) = ((term7 _17370 _17371 P Q) = (term8 _17370 _17371 P Q)).
Proof. exact (MK_COMB (@lem511077 _17370 _17371 P Q) (@lem511064 _17370 _17371 P Q)). Qed.
Lemma lem511079 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) : (term10 _17370 _17371 Q) = (term10 _17370 _17371 Q).
Proof. exact (fun_ext (fun P : _17371 -> Prop => @lem511078 _17370 _17371 P Q)). Qed.
Lemma lem511080 {_17371 : Type'} : (@all (_17371 -> Prop)) = (@all (_17371 -> Prop)).
Proof. exact (eq_refl (@all (_17371 -> Prop))). Qed.
Lemma lem511081 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) : (term12 _17370 _17371 Q) = (term12 _17370 _17371 Q).
Proof. exact (MK_COMB (@lem511080 _17371) (@lem511079 _17370 _17371 Q)). Qed.
Lemma lem511082 {_17370 _17371 : Type'} : (term14 _17370 _17371) = (term14 _17370 _17371).
Proof. exact (fun_ext (fun Q : type1470 _17370 _17371 => @lem511081 _17370 _17371 Q)). Qed.
Lemma lem511083 {_17370 _17371 : Type'} : (@all (_17371 -> _17370 -> Prop)) = (@all (_17371 -> _17370 -> Prop)).
Proof. exact (eq_refl (@all (_17371 -> _17370 -> Prop))). Qed.
Lemma lem511084 {_17370 _17371 : Type'} : (term16 _17370 _17371) = (term16 _17370 _17371).
Proof. exact (MK_COMB (@lem511083 _17370 _17371) (@lem511082 _17370 _17371)). Qed.
Lemma lem511127 {_17370 _17371 : Type'} : (term15 _17370 _17371) = (term16 _17370 _17371).
Proof. exact (TRANS (@lem511053 _17370 _17371) (@lem511084 _17370 _17371)). Qed.
Lemma lem511128 {_17370 _17371 : Type'} : (term16 _17370 _17371) = (term15 _17370 _17371).
Proof. exact (SYM (@lem511127 _17370 _17371)). Qed.
Lemma lem511130 (p : Prop) : p = (term27 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem511131 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : ((term7 _17370 _17371 P Q) = (term8 _17370 _17371 P Q)) = (term1 _17370 _17371 P Q).
Proof. exact (@lem511130 ((term7 _17370 _17371 P Q) = (term8 _17370 _17371 P Q))). Qed.
Lemma lem511132 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term1 _17370 _17371 P Q) = ((term7 _17370 _17371 P Q) = (term8 _17370 _17371 P Q)).
Proof. exact (SYM (@lem511131 _17370 _17371 P Q)). Qed.
Lemma lem511133 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term0 _17370 _17371 P Q) : term0 _17370 _17371 P Q.
Proof. exact (h1). Qed.
Lemma lem511137 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (Q x y) = (Q x y).
Proof. exact (eq_refl (Q x y)). Qed.
Lemma lem511138 {_17370 : Type'} (P : _17370 -> Prop) : (term28 _17370 P) = (term29 _17370 P).
Proof. exact (@lem18392 _17370 P). Qed.
Lemma lem511139 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) : (term30 _17370 _17371 Q x) = (term31 _17370 _17371 Q x).
Proof. exact (@lem511138 _17370 (term21 _17370 _17371 Q x)). Qed.
Lemma lem511140 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term32 _17370 _17371 Q x y) = (Q x y).
Proof. exact (eq_refl (term32 _17370 _17371 Q x y)). Qed.
Lemma lem511141 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem511143 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term33 _17370 _17371 Q x y) = (term34 _17370 _17371 Q x y).
Proof. exact (MK_COMB (@lem511141) (@lem511140 _17370 _17371 Q x y)). Qed.
Lemma lem511144 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) : (term35 _17370 _17371 Q x) = (term36 _17370 _17371 Q x).
Proof. exact (fun_ext (fun y : _17370 => @lem511143 _17370 _17371 Q x y)). Qed.
Lemma lem511145 {_17370 : Type'} : (@ex _17370) = (@ex _17370).
Proof. exact (eq_refl (@ex _17370)). Qed.
Lemma lem511146 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) : (term31 _17370 _17371 Q x) = (term37 _17370 _17371 Q x).
Proof. exact (MK_COMB (@lem511145 _17370) (@lem511144 _17370 _17371 Q x)). Qed.
Lemma lem511147 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) : (term30 _17370 _17371 Q x) = (term37 _17370 _17371 Q x).
Proof. exact (TRANS (@lem511139 _17370 _17371 Q x) (@lem511146 _17370 _17371 Q x)). Qed.
Lemma lem511148 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) : (term21 _17370 _17371 Q x) = (term21 _17370 _17371 Q x).
Proof. exact (fun_ext (fun y : _17370 => @lem511137 _17370 _17371 Q x y)). Qed.
Lemma lem511149 {_17370 : Type'} : (@all _17370) = (@all _17370).
Proof. exact (eq_refl (@all _17370)). Qed.
Lemma lem511150 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) : (term22 _17370 _17371 Q x) = (term22 _17370 _17371 Q x).
Proof. exact (MK_COMB (@lem511149 _17370) (@lem511148 _17370 _17371 Q x)). Qed.
Lemma lem511152 {_17371 : Type'} (P : _17371 -> Prop) (x : _17371) : (term38 _17371 P x) = (term38 _17371 P x).
Proof. exact (eq_refl (term38 _17371 P x)). Qed.
Lemma lem511153 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term39 _17370 _17371 P Q x) = (term40 _17370 _17371 P Q x).
Proof. exact (MK_COMB (@lem511152 _17371 P x) (@lem511147 _17370 _17371 Q x)). Qed.
Lemma lem511154 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term41 _17370 _17371 P Q x) = (term39 _17370 _17371 P Q x).
Proof. exact (@lem17362 (P x) (term22 _17370 _17371 Q x)). Qed.
Lemma lem511155 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term41 _17370 _17371 P Q x) = (term40 _17370 _17371 P Q x).
Proof. exact (TRANS (@lem511154 _17370 _17371 P Q x) (@lem511153 _17370 _17371 P Q x)). Qed.
Lemma lem511157 {_17371 : Type'} (P : _17371 -> Prop) (x : _17371) : (term42 _17371 P x) = (term42 _17371 P x).
Proof. exact (eq_refl (term42 _17371 P x)). Qed.
Lemma lem511158 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term43 _17370 _17371 P Q x) = (term43 _17370 _17371 P Q x).
Proof. exact (MK_COMB (@lem511157 _17371 P x) (@lem511150 _17370 _17371 Q x)). Qed.
Lemma lem511159 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term24 _17370 _17371 P Q x) = (term43 _17370 _17371 P Q x).
Proof. exact (@lem17265 (P x) (term22 _17370 _17371 Q x)). Qed.
Lemma lem511160 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term24 _17370 _17371 P Q x) = (term43 _17370 _17371 P Q x).
Proof. exact (TRANS (@lem511159 _17370 _17371 P Q x) (@lem511158 _17370 _17371 P Q x)). Qed.
Lemma lem511161 {_17371 : Type'} (P : _17371 -> Prop) : (term28 _17371 P) = (term29 _17371 P).
Proof. exact (@lem18392 _17371 P). Qed.
Lemma lem511162 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term44 _17370 _17371 P Q) = (term45 _17370 _17371 P Q).
Proof. exact (@lem511161 _17371 (term25 _17370 _17371 P Q)). Qed.
Lemma lem511163 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term46 _17370 _17371 P Q x) = (term24 _17370 _17371 P Q x).
Proof. exact (eq_refl (term46 _17370 _17371 P Q x)). Qed.
Lemma lem511164 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem511165 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term47 _17370 _17371 P Q x) = (term41 _17370 _17371 P Q x).
Proof. exact (MK_COMB (@lem511164) (@lem511163 _17370 _17371 P Q x)). Qed.
Lemma lem511166 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term47 _17370 _17371 P Q x) = (term40 _17370 _17371 P Q x).
Proof. exact (TRANS (@lem511165 _17370 _17371 P Q x) (@lem511155 _17370 _17371 P Q x)). Qed.
Lemma lem511167 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term48 _17370 _17371 P Q) = (term49 _17370 _17371 P Q).
Proof. exact (fun_ext (fun x : _17371 => @lem511166 _17370 _17371 P Q x)). Qed.
Lemma lem511168 {_17371 : Type'} : (@ex _17371) = (@ex _17371).
Proof. exact (eq_refl (@ex _17371)). Qed.
Lemma lem511169 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term45 _17370 _17371 P Q) = (term50 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511168 _17371) (@lem511167 _17370 _17371 P Q)). Qed.
Lemma lem511170 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term44 _17370 _17371 P Q) = (term50 _17370 _17371 P Q).
Proof. exact (TRANS (@lem511162 _17370 _17371 P Q) (@lem511169 _17370 _17371 P Q)). Qed.
Lemma lem511171 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term25 _17370 _17371 P Q) = (term51 _17370 _17371 P Q).
Proof. exact (fun_ext (fun x : _17371 => @lem511160 _17370 _17371 P Q x)). Qed.
Lemma lem511172 {_17371 : Type'} : (@all _17371) = (@all _17371).
Proof. exact (eq_refl (@all _17371)). Qed.
Lemma lem511173 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term7 _17370 _17371 P Q) = (term52 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511172 _17371) (@lem511171 _17370 _17371 P Q)). Qed.
Lemma lem511182 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term53 _17370 _17371 P Q x y) = (term54 _17370 _17371 P Q x y).
Proof. exact (@lem17362 (P x) (Q x y)). Qed.
Lemma lem511187 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term17 _17370 _17371 P Q x y) = (term55 _17370 _17371 P Q x y).
Proof. exact (@lem17265 (P x) (Q x y)). Qed.
Lemma lem511188 {_17371 : Type'} (P : _17371 -> Prop) : (term28 _17371 P) = (term29 _17371 P).
Proof. exact (@lem18392 _17371 P). Qed.
Lemma lem511189 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term56 _17370 _17371 P Q y) = (term57 _17370 _17371 P Q y).
Proof. exact (@lem511188 _17371 (term18 _17370 _17371 P Q y)). Qed.
Lemma lem511190 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term58 _17370 _17371 P Q y x) = (term17 _17370 _17371 P Q x y).
Proof. exact (eq_refl (term58 _17370 _17371 P Q y x)). Qed.
Lemma lem511191 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem511192 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term59 _17370 _17371 P Q y x) = (term53 _17370 _17371 P Q x y).
Proof. exact (MK_COMB (@lem511191) (@lem511190 _17370 _17371 P Q x y)). Qed.
Lemma lem511193 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term59 _17370 _17371 P Q y x) = (term54 _17370 _17371 P Q x y).
Proof. exact (TRANS (@lem511192 _17370 _17371 P Q x y) (@lem511182 _17370 _17371 P Q x y)). Qed.
Lemma lem511194 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term60 _17370 _17371 P Q y) = (term61 _17370 _17371 P Q y).
Proof. exact (fun_ext (fun x : _17371 => @lem511193 _17370 _17371 P Q x y)). Qed.
Lemma lem511195 {_17371 : Type'} : (@ex _17371) = (@ex _17371).
Proof. exact (eq_refl (@ex _17371)). Qed.
Lemma lem511196 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term57 _17370 _17371 P Q y) = (term62 _17370 _17371 P Q y).
Proof. exact (MK_COMB (@lem511195 _17371) (@lem511194 _17370 _17371 P Q y)). Qed.
Lemma lem511197 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term56 _17370 _17371 P Q y) = (term62 _17370 _17371 P Q y).
Proof. exact (TRANS (@lem511189 _17370 _17371 P Q y) (@lem511196 _17370 _17371 P Q y)). Qed.
Lemma lem511198 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term18 _17370 _17371 P Q y) = (term63 _17370 _17371 P Q y).
Proof. exact (fun_ext (fun x : _17371 => @lem511187 _17370 _17371 P Q x y)). Qed.
Lemma lem511199 {_17371 : Type'} : (@all _17371) = (@all _17371).
Proof. exact (eq_refl (@all _17371)). Qed.
Lemma lem511200 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term19 _17370 _17371 P Q y) = (term64 _17370 _17371 P Q y).
Proof. exact (MK_COMB (@lem511199 _17371) (@lem511198 _17370 _17371 P Q y)). Qed.
Lemma lem511201 {_17370 : Type'} (P : _17370 -> Prop) : (term28 _17370 P) = (term29 _17370 P).
Proof. exact (@lem18392 _17370 P). Qed.
Lemma lem511202 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term65 _17370 _17371 P Q) = (term66 _17370 _17371 P Q).
Proof. exact (@lem511201 _17370 (term20 _17370 _17371 P Q)). Qed.
Lemma lem511203 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term67 _17370 _17371 P Q y) = (term19 _17370 _17371 P Q y).
Proof. exact (eq_refl (term67 _17370 _17371 P Q y)). Qed.
Lemma lem511204 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem511205 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term68 _17370 _17371 P Q y) = (term56 _17370 _17371 P Q y).
Proof. exact (MK_COMB (@lem511204) (@lem511203 _17370 _17371 P Q y)). Qed.
Lemma lem511206 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term68 _17370 _17371 P Q y) = (term62 _17370 _17371 P Q y).
Proof. exact (TRANS (@lem511205 _17370 _17371 P Q y) (@lem511197 _17370 _17371 P Q y)). Qed.
Lemma lem511207 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term69 _17370 _17371 P Q) = (term70 _17370 _17371 P Q).
Proof. exact (fun_ext (fun y : _17370 => @lem511206 _17370 _17371 P Q y)). Qed.
Lemma lem511208 {_17370 : Type'} : (@ex _17370) = (@ex _17370).
Proof. exact (eq_refl (@ex _17370)). Qed.
Lemma lem511209 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term66 _17370 _17371 P Q) = (term71 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511208 _17370) (@lem511207 _17370 _17371 P Q)). Qed.
Lemma lem511210 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term65 _17370 _17371 P Q) = (term71 _17370 _17371 P Q).
Proof. exact (TRANS (@lem511202 _17370 _17371 P Q) (@lem511209 _17370 _17371 P Q)). Qed.
Lemma lem511211 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term20 _17370 _17371 P Q) = (term72 _17370 _17371 P Q).
Proof. exact (fun_ext (fun y : _17370 => @lem511200 _17370 _17371 P Q y)). Qed.
Lemma lem511212 {_17370 : Type'} : (@all _17370) = (@all _17370).
Proof. exact (eq_refl (@all _17370)). Qed.
Lemma lem511213 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term8 _17370 _17371 P Q) = (term73 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511212 _17370) (@lem511211 _17370 _17371 P Q)). Qed.
Lemma lem511214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem511215 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term74 _17370 _17371 P Q) = (term75 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511214) (@lem511170 _17370 _17371 P Q)). Qed.
Lemma lem511216 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term76 _17370 _17371 P Q) = (term77 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511215 _17370 _17371 P Q) (@lem511213 _17370 _17371 P Q)). Qed.
Lemma lem511217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem511218 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term78 _17370 _17371 P Q) = (term79 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511217) (@lem511173 _17370 _17371 P Q)). Qed.
Lemma lem511219 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term80 _17370 _17371 P Q) = (term81 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511218 _17370 _17371 P Q) (@lem511210 _17370 _17371 P Q)). Qed.
Lemma lem511220 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem511221 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term82 _17370 _17371 P Q) = (term83 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511220) (@lem511219 _17370 _17371 P Q)). Qed.
Lemma lem511222 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term84 _17370 _17371 P Q) = (term85 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511221 _17370 _17371 P Q) (@lem511216 _17370 _17371 P Q)). Qed.
Lemma lem511223 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term0 _17370 _17371 P Q) = (term84 _17370 _17371 P Q).
Proof. exact (@lem17646 (term7 _17370 _17371 P Q) (term8 _17370 _17371 P Q)). Qed.
Lemma lem511224 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term0 _17370 _17371 P Q) = (term85 _17370 _17371 P Q).
Proof. exact (TRANS (@lem511223 _17370 _17371 P Q) (@lem511222 _17370 _17371 P Q)). Qed.
Lemma lem511395 {A : Type'} (P : Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem511396 {_17370 : Type'} (P : Prop) (Q : _17370 -> Prop) : (term86 _17370 P Q) = (term87 _17370 P Q).
Proof. exact (@lem511395 _17370 P Q). Qed.
Lemma lem511397 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term88 _17370 _17371 P Q) = (term89 _17370 _17371 P Q).
Proof. exact (@lem511396 _17370 (term52 _17370 _17371 P Q) (term70 _17370 _17371 P Q)). Qed.
Lemma lem511398 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term90 _17370 _17371 P Q y) = (term62 _17370 _17371 P Q y).
Proof. exact (eq_refl (term90 _17370 _17371 P Q y)). Qed.
Lemma lem511399 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term91 _17370 _17371 P Q) = (term70 _17370 _17371 P Q).
Proof. exact (fun_ext (fun y : _17370 => @lem511398 _17370 _17371 P Q y)). Qed.
Lemma lem511400 {_17370 : Type'} : (@ex _17370) = (@ex _17370).
Proof. exact (eq_refl (@ex _17370)). Qed.
Lemma lem511401 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term92 _17370 _17371 P Q) = (term71 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511400 _17370) (@lem511399 _17370 _17371 P Q)). Qed.
Lemma lem511402 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term79 _17370 _17371 P Q) = (term79 _17370 _17371 P Q).
Proof. exact (eq_refl (term79 _17370 _17371 P Q)). Qed.
Lemma lem511403 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term88 _17370 _17371 P Q) = (term81 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511402 _17370 _17371 P Q) (@lem511401 _17370 _17371 P Q)). Qed.
Lemma lem511404 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem511405 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term93 _17370 _17371 P Q) = (term94 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511404) (@lem511403 _17370 _17371 P Q)). Qed.
Lemma lem511406 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term90 _17370 _17371 P Q y) = (term62 _17370 _17371 P Q y).
Proof. exact (eq_refl (term90 _17370 _17371 P Q y)). Qed.
Lemma lem511407 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term79 _17370 _17371 P Q) = (term79 _17370 _17371 P Q).
Proof. exact (eq_refl (term79 _17370 _17371 P Q)). Qed.
Lemma lem511408 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term95 _17370 _17371 P Q y) = (term96 _17370 _17371 P Q y).
Proof. exact (MK_COMB (@lem511407 _17370 _17371 P Q) (@lem511406 _17370 _17371 P Q y)). Qed.
Lemma lem511409 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term97 _17370 _17371 P Q) = (term98 _17370 _17371 P Q).
Proof. exact (fun_ext (fun y : _17370 => @lem511408 _17370 _17371 P Q y)). Qed.
Lemma lem511410 {_17370 : Type'} : (@ex _17370) = (@ex _17370).
Proof. exact (eq_refl (@ex _17370)). Qed.
Lemma lem511411 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term89 _17370 _17371 P Q) = (term99 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511410 _17370) (@lem511409 _17370 _17371 P Q)). Qed.
Lemma lem511412 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : ((term88 _17370 _17371 P Q) = (term89 _17370 _17371 P Q)) = ((term81 _17370 _17371 P Q) = (term99 _17370 _17371 P Q)).
Proof. exact (MK_COMB (@lem511405 _17370 _17371 P Q) (@lem511411 _17370 _17371 P Q)). Qed.
Lemma lem511413 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term81 _17370 _17371 P Q) = (term99 _17370 _17371 P Q).
Proof. exact (EQ_MP (@lem511412 _17370 _17371 P Q) (@lem511397 _17370 _17371 P Q)). Qed.
Lemma lem511415 {A : Type'} (P : Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem511416 {_17371 : Type'} (P : Prop) (Q : _17371 -> Prop) : (term86 _17371 P Q) = (term87 _17371 P Q).
Proof. exact (@lem511415 _17371 P Q). Qed.
Lemma lem511417 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term100 _17370 _17371 P Q y) = (term101 _17370 _17371 P Q y).
Proof. exact (@lem511416 _17371 (term52 _17370 _17371 P Q) (term61 _17370 _17371 P Q y)). Qed.
Lemma lem511418 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term102 _17370 _17371 P Q y x) = (term54 _17370 _17371 P Q x y).
Proof. exact (eq_refl (term102 _17370 _17371 P Q y x)). Qed.
Lemma lem511419 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term103 _17370 _17371 P Q y) = (term61 _17370 _17371 P Q y).
Proof. exact (fun_ext (fun x : _17371 => @lem511418 _17370 _17371 P Q x y)). Qed.
Lemma lem511420 {_17371 : Type'} : (@ex _17371) = (@ex _17371).
Proof. exact (eq_refl (@ex _17371)). Qed.
Lemma lem511421 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term104 _17370 _17371 P Q y) = (term62 _17370 _17371 P Q y).
Proof. exact (MK_COMB (@lem511420 _17371) (@lem511419 _17370 _17371 P Q y)). Qed.
Lemma lem511422 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term79 _17370 _17371 P Q) = (term79 _17370 _17371 P Q).
Proof. exact (eq_refl (term79 _17370 _17371 P Q)). Qed.
Lemma lem511423 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term100 _17370 _17371 P Q y) = (term96 _17370 _17371 P Q y).
Proof. exact (MK_COMB (@lem511422 _17370 _17371 P Q) (@lem511421 _17370 _17371 P Q y)). Qed.
Lemma lem511424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem511425 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term105 _17370 _17371 P Q y) = (term106 _17370 _17371 P Q y).
Proof. exact (MK_COMB (@lem511424) (@lem511423 _17370 _17371 P Q y)). Qed.
Lemma lem511426 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term102 _17370 _17371 P Q y x) = (term54 _17370 _17371 P Q x y).
Proof. exact (eq_refl (term102 _17370 _17371 P Q y x)). Qed.
Lemma lem511427 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term79 _17370 _17371 P Q) = (term79 _17370 _17371 P Q).
Proof. exact (eq_refl (term79 _17370 _17371 P Q)). Qed.
Lemma lem511428 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term107 _17370 _17371 P Q y x) = (term108 _17370 _17371 P Q x y).
Proof. exact (MK_COMB (@lem511427 _17370 _17371 P Q) (@lem511426 _17370 _17371 P Q x y)). Qed.
Lemma lem511429 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term109 _17370 _17371 P Q y) = (term110 _17370 _17371 P Q y).
Proof. exact (fun_ext (fun x : _17371 => @lem511428 _17370 _17371 P Q x y)). Qed.
Lemma lem511430 {_17371 : Type'} : (@ex _17371) = (@ex _17371).
Proof. exact (eq_refl (@ex _17371)). Qed.
Lemma lem511431 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term101 _17370 _17371 P Q y) = (term111 _17370 _17371 P Q y).
Proof. exact (MK_COMB (@lem511430 _17371) (@lem511429 _17370 _17371 P Q y)). Qed.
Lemma lem511432 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : ((term100 _17370 _17371 P Q y) = (term101 _17370 _17371 P Q y)) = ((term96 _17370 _17371 P Q y) = (term111 _17370 _17371 P Q y)).
Proof. exact (MK_COMB (@lem511425 _17370 _17371 P Q y) (@lem511431 _17370 _17371 P Q y)). Qed.
Lemma lem511433 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term96 _17370 _17371 P Q y) = (term111 _17370 _17371 P Q y).
Proof. exact (EQ_MP (@lem511432 _17370 _17371 P Q y) (@lem511417 _17370 _17371 P Q y)). Qed.
Lemma lem511434 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term98 _17370 _17371 P Q) = (term112 _17370 _17371 P Q).
Proof. exact (fun_ext (fun y : _17370 => @lem511433 _17370 _17371 P Q y)). Qed.
Lemma lem511435 {_17370 : Type'} : (@ex _17370) = (@ex _17370).
Proof. exact (eq_refl (@ex _17370)). Qed.
Lemma lem511436 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term99 _17370 _17371 P Q) = (term113 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511435 _17370) (@lem511434 _17370 _17371 P Q)). Qed.
Lemma lem511437 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term81 _17370 _17371 P Q) = (term113 _17370 _17371 P Q).
Proof. exact (TRANS (@lem511413 _17370 _17371 P Q) (@lem511436 _17370 _17371 P Q)). Qed.
Lemma lem511438 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem511439 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term83 _17370 _17371 P Q) = (term114 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511438) (@lem511437 _17370 _17371 P Q)). Qed.
Lemma lem511441 {A : Type'} (P : Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem511442 {_17370 : Type'} (P : Prop) (Q : _17370 -> Prop) : (term86 _17370 P Q) = (term87 _17370 P Q).
Proof. exact (@lem511441 _17370 P Q). Qed.
Lemma lem511443 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term115 _17370 _17371 P Q x) = (term116 _17370 _17371 P Q x).
Proof. exact (@lem511442 _17370 (P x) (term36 _17370 _17371 Q x)). Qed.
Lemma lem511444 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term117 _17370 _17371 Q x y) = (term34 _17370 _17371 Q x y).
Proof. exact (eq_refl (term117 _17370 _17371 Q x y)). Qed.
Lemma lem511445 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) : (term118 _17370 _17371 Q x) = (term36 _17370 _17371 Q x).
Proof. exact (fun_ext (fun y : _17370 => @lem511444 _17370 _17371 Q x y)). Qed.
Lemma lem511446 {_17370 : Type'} : (@ex _17370) = (@ex _17370).
Proof. exact (eq_refl (@ex _17370)). Qed.
Lemma lem511447 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) : (term119 _17370 _17371 Q x) = (term37 _17370 _17371 Q x).
Proof. exact (MK_COMB (@lem511446 _17370) (@lem511445 _17370 _17371 Q x)). Qed.
Lemma lem511448 {_17371 : Type'} (P : _17371 -> Prop) (x : _17371) : (term38 _17371 P x) = (term38 _17371 P x).
Proof. exact (eq_refl (term38 _17371 P x)). Qed.
Lemma lem511449 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term115 _17370 _17371 P Q x) = (term40 _17370 _17371 P Q x).
Proof. exact (MK_COMB (@lem511448 _17371 P x) (@lem511447 _17370 _17371 Q x)). Qed.
Lemma lem511450 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem511451 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term120 _17370 _17371 P Q x) = (term121 _17370 _17371 P Q x).
Proof. exact (MK_COMB (@lem511450) (@lem511449 _17370 _17371 P Q x)). Qed.
Lemma lem511452 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term117 _17370 _17371 Q x y) = (term34 _17370 _17371 Q x y).
Proof. exact (eq_refl (term117 _17370 _17371 Q x y)). Qed.
Lemma lem511453 {_17371 : Type'} (P : _17371 -> Prop) (x : _17371) : (term38 _17371 P x) = (term38 _17371 P x).
Proof. exact (eq_refl (term38 _17371 P x)). Qed.
Lemma lem511454 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term122 _17370 _17371 P Q x y) = (term54 _17370 _17371 P Q x y).
Proof. exact (MK_COMB (@lem511453 _17371 P x) (@lem511452 _17370 _17371 Q x y)). Qed.
Lemma lem511455 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term123 _17370 _17371 P Q x) = (term124 _17370 _17371 P Q x).
Proof. exact (fun_ext (fun y : _17370 => @lem511454 _17370 _17371 P Q x y)). Qed.
Lemma lem511456 {_17370 : Type'} : (@ex _17370) = (@ex _17370).
Proof. exact (eq_refl (@ex _17370)). Qed.
Lemma lem511457 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term116 _17370 _17371 P Q x) = (term125 _17370 _17371 P Q x).
Proof. exact (MK_COMB (@lem511456 _17370) (@lem511455 _17370 _17371 P Q x)). Qed.
Lemma lem511458 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : ((term115 _17370 _17371 P Q x) = (term116 _17370 _17371 P Q x)) = ((term40 _17370 _17371 P Q x) = (term125 _17370 _17371 P Q x)).
Proof. exact (MK_COMB (@lem511451 _17370 _17371 P Q x) (@lem511457 _17370 _17371 P Q x)). Qed.
Lemma lem511459 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term40 _17370 _17371 P Q x) = (term125 _17370 _17371 P Q x).
Proof. exact (EQ_MP (@lem511458 _17370 _17371 P Q x) (@lem511443 _17370 _17371 P Q x)). Qed.
Lemma lem511460 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term49 _17370 _17371 P Q) = (term126 _17370 _17371 P Q).
Proof. exact (fun_ext (fun x : _17371 => @lem511459 _17370 _17371 P Q x)). Qed.
Lemma lem511461 {_17371 : Type'} : (@ex _17371) = (@ex _17371).
Proof. exact (eq_refl (@ex _17371)). Qed.
Lemma lem511462 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term50 _17370 _17371 P Q) = (term127 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511461 _17371) (@lem511460 _17370 _17371 P Q)). Qed.
Lemma lem511463 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem511464 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term75 _17370 _17371 P Q) = (term128 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511463) (@lem511462 _17370 _17371 P Q)). Qed.
Lemma lem511465 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term73 _17370 _17371 P Q) = (term73 _17370 _17371 P Q).
Proof. exact (eq_refl (term73 _17370 _17371 P Q)). Qed.
Lemma lem511466 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term77 _17370 _17371 P Q) = (term129 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511464 _17370 _17371 P Q) (@lem511465 _17370 _17371 P Q)). Qed.
Lemma lem511468 {A : Type'} (P : A -> Prop) (Q : Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem511469 {_17371 : Type'} (P : _17371 -> Prop) (Q : Prop) : (term130 _17371 P Q) = (term131 _17371 P Q).
Proof. exact (@lem511468 _17371 P Q). Qed.
Lemma lem511470 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term132 _17370 _17371 P Q) = (term133 _17370 _17371 P Q).
Proof. exact (@lem511469 _17371 (term126 _17370 _17371 P Q) (term73 _17370 _17371 P Q)). Qed.
Lemma lem511471 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term134 _17370 _17371 P Q x) = (term125 _17370 _17371 P Q x).
Proof. exact (eq_refl (term134 _17370 _17371 P Q x)). Qed.
Lemma lem511472 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term135 _17370 _17371 P Q) = (term126 _17370 _17371 P Q).
Proof. exact (fun_ext (fun x : _17371 => @lem511471 _17370 _17371 P Q x)). Qed.
Lemma lem511473 {_17371 : Type'} : (@ex _17371) = (@ex _17371).
Proof. exact (eq_refl (@ex _17371)). Qed.
Lemma lem511474 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term136 _17370 _17371 P Q) = (term127 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511473 _17371) (@lem511472 _17370 _17371 P Q)). Qed.
Lemma lem511475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem511476 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term137 _17370 _17371 P Q) = (term128 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511475) (@lem511474 _17370 _17371 P Q)). Qed.
Lemma lem511477 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term73 _17370 _17371 P Q) = (term73 _17370 _17371 P Q).
Proof. exact (eq_refl (term73 _17370 _17371 P Q)). Qed.
Lemma lem511478 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term132 _17370 _17371 P Q) = (term129 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511476 _17370 _17371 P Q) (@lem511477 _17370 _17371 P Q)). Qed.
Lemma lem511479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem511480 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term138 _17370 _17371 P Q) = (term139 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511479) (@lem511478 _17370 _17371 P Q)). Qed.
Lemma lem511481 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term134 _17370 _17371 P Q x) = (term125 _17370 _17371 P Q x).
Proof. exact (eq_refl (term134 _17370 _17371 P Q x)). Qed.
Lemma lem511482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem511483 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term140 _17370 _17371 P Q x) = (term141 _17370 _17371 P Q x).
Proof. exact (MK_COMB (@lem511482) (@lem511481 _17370 _17371 P Q x)). Qed.
Lemma lem511484 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term73 _17370 _17371 P Q) = (term73 _17370 _17371 P Q).
Proof. exact (eq_refl (term73 _17370 _17371 P Q)). Qed.
Lemma lem511485 {_17370 _17371 : Type'} (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term142 _17370 _17371 x P Q) = (term143 _17370 _17371 x P Q).
Proof. exact (MK_COMB (@lem511483 _17370 _17371 P Q x) (@lem511484 _17370 _17371 P Q)). Qed.
Lemma lem511486 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term144 _17370 _17371 P Q) = (term145 _17370 _17371 P Q).
Proof. exact (fun_ext (fun x : _17371 => @lem511485 _17370 _17371 x P Q)). Qed.
Lemma lem511487 {_17371 : Type'} : (@ex _17371) = (@ex _17371).
Proof. exact (eq_refl (@ex _17371)). Qed.
Lemma lem511488 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term133 _17370 _17371 P Q) = (term146 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511487 _17371) (@lem511486 _17370 _17371 P Q)). Qed.
Lemma lem511489 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : ((term132 _17370 _17371 P Q) = (term133 _17370 _17371 P Q)) = ((term129 _17370 _17371 P Q) = (term146 _17370 _17371 P Q)).
Proof. exact (MK_COMB (@lem511480 _17370 _17371 P Q) (@lem511488 _17370 _17371 P Q)). Qed.
Lemma lem511490 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term129 _17370 _17371 P Q) = (term146 _17370 _17371 P Q).
Proof. exact (EQ_MP (@lem511489 _17370 _17371 P Q) (@lem511470 _17370 _17371 P Q)). Qed.
Lemma lem511492 {A : Type'} (P : A -> Prop) (Q : Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem511493 {_17370 : Type'} (P : _17370 -> Prop) (Q : Prop) : (term130 _17370 P Q) = (term131 _17370 P Q).
Proof. exact (@lem511492 _17370 P Q). Qed.
Lemma lem511494 {_17370 _17371 : Type'} (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term147 _17370 _17371 x P Q) = (term148 _17370 _17371 x P Q).
Proof. exact (@lem511493 _17370 (term124 _17370 _17371 P Q x) (term73 _17370 _17371 P Q)). Qed.
Lemma lem511495 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term149 _17370 _17371 P Q x y) = (term54 _17370 _17371 P Q x y).
Proof. exact (eq_refl (term149 _17370 _17371 P Q x y)). Qed.
Lemma lem511496 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term150 _17370 _17371 P Q x) = (term124 _17370 _17371 P Q x).
Proof. exact (fun_ext (fun y : _17370 => @lem511495 _17370 _17371 P Q x y)). Qed.
Lemma lem511497 {_17370 : Type'} : (@ex _17370) = (@ex _17370).
Proof. exact (eq_refl (@ex _17370)). Qed.
Lemma lem511498 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term151 _17370 _17371 P Q x) = (term125 _17370 _17371 P Q x).
Proof. exact (MK_COMB (@lem511497 _17370) (@lem511496 _17370 _17371 P Q x)). Qed.
Lemma lem511499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem511500 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term152 _17370 _17371 P Q x) = (term141 _17370 _17371 P Q x).
Proof. exact (MK_COMB (@lem511499) (@lem511498 _17370 _17371 P Q x)). Qed.
Lemma lem511501 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term73 _17370 _17371 P Q) = (term73 _17370 _17371 P Q).
Proof. exact (eq_refl (term73 _17370 _17371 P Q)). Qed.
Lemma lem511502 {_17370 _17371 : Type'} (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term147 _17370 _17371 x P Q) = (term143 _17370 _17371 x P Q).
Proof. exact (MK_COMB (@lem511500 _17370 _17371 P Q x) (@lem511501 _17370 _17371 P Q)). Qed.
Lemma lem511503 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem511504 {_17370 _17371 : Type'} (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term153 _17370 _17371 x P Q) = (term154 _17370 _17371 x P Q).
Proof. exact (MK_COMB (@lem511503) (@lem511502 _17370 _17371 x P Q)). Qed.
Lemma lem511505 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term149 _17370 _17371 P Q x y) = (term54 _17370 _17371 P Q x y).
Proof. exact (eq_refl (term149 _17370 _17371 P Q x y)). Qed.
Lemma lem511506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem511507 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term155 _17370 _17371 P Q x y) = (term156 _17370 _17371 P Q x y).
Proof. exact (MK_COMB (@lem511506) (@lem511505 _17370 _17371 P Q x y)). Qed.
Lemma lem511508 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term73 _17370 _17371 P Q) = (term73 _17370 _17371 P Q).
Proof. exact (eq_refl (term73 _17370 _17371 P Q)). Qed.
Lemma lem511509 {_17370 _17371 : Type'} (x : _17371) (y : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term157 _17370 _17371 x y P Q) = (term158 _17370 _17371 x y P Q).
Proof. exact (MK_COMB (@lem511507 _17370 _17371 P Q x y) (@lem511508 _17370 _17371 P Q)). Qed.
Lemma lem511510 {_17370 _17371 : Type'} (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term159 _17370 _17371 x P Q) = (term160 _17370 _17371 x P Q).
Proof. exact (fun_ext (fun y : _17370 => @lem511509 _17370 _17371 x y P Q)). Qed.
Lemma lem511511 {_17370 : Type'} : (@ex _17370) = (@ex _17370).
Proof. exact (eq_refl (@ex _17370)). Qed.
Lemma lem511512 {_17370 _17371 : Type'} (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term148 _17370 _17371 x P Q) = (term161 _17370 _17371 x P Q).
Proof. exact (MK_COMB (@lem511511 _17370) (@lem511510 _17370 _17371 x P Q)). Qed.
Lemma lem511513 {_17370 _17371 : Type'} (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : ((term147 _17370 _17371 x P Q) = (term148 _17370 _17371 x P Q)) = ((term143 _17370 _17371 x P Q) = (term161 _17370 _17371 x P Q)).
Proof. exact (MK_COMB (@lem511504 _17370 _17371 x P Q) (@lem511512 _17370 _17371 x P Q)). Qed.
Lemma lem511514 {_17370 _17371 : Type'} (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term143 _17370 _17371 x P Q) = (term161 _17370 _17371 x P Q).
Proof. exact (EQ_MP (@lem511513 _17370 _17371 x P Q) (@lem511494 _17370 _17371 x P Q)). Qed.
Lemma lem511515 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term145 _17370 _17371 P Q) = (term162 _17370 _17371 P Q).
Proof. exact (fun_ext (fun x : _17371 => @lem511514 _17370 _17371 x P Q)). Qed.
Lemma lem511516 {_17371 : Type'} : (@ex _17371) = (@ex _17371).
Proof. exact (eq_refl (@ex _17371)). Qed.
Lemma lem511517 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term146 _17370 _17371 P Q) = (term163 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511516 _17371) (@lem511515 _17370 _17371 P Q)). Qed.
Lemma lem511518 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term129 _17370 _17371 P Q) = (term163 _17370 _17371 P Q).
Proof. exact (TRANS (@lem511490 _17370 _17371 P Q) (@lem511517 _17370 _17371 P Q)). Qed.
Lemma lem511519 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term77 _17370 _17371 P Q) = (term163 _17370 _17371 P Q).
Proof. exact (TRANS (@lem511466 _17370 _17371 P Q) (@lem511518 _17370 _17371 P Q)). Qed.
Lemma lem511520 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term85 _17370 _17371 P Q) = (term164 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511439 _17370 _17371 P Q) (@lem511519 _17370 _17371 P Q)). Qed.
Lemma lem511524 {A : Type'} (P : A -> Prop) (Q : Prop) : (term165 A P Q) = (term166 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem511525 {_17370 : Type'} (P : _17370 -> Prop) (Q : Prop) : (term165 _17370 P Q) = (term166 _17370 P Q).
Proof. exact (@lem511524 _17370 P Q). Qed.
Lemma lem511526 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term167 _17370 _17371 P Q) = (term168 _17370 _17371 P Q).
Proof. exact (@lem511525 _17370 (term112 _17370 _17371 P Q) (term163 _17370 _17371 P Q)). Qed.
Lemma lem511527 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term169 _17370 _17371 P Q y) = (term111 _17370 _17371 P Q y).
Proof. exact (eq_refl (term169 _17370 _17371 P Q y)). Qed.
Lemma lem511528 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term170 _17370 _17371 P Q) = (term112 _17370 _17371 P Q).
Proof. exact (fun_ext (fun y : _17370 => @lem511527 _17370 _17371 P Q y)). Qed.
Lemma lem511529 {_17370 : Type'} : (@ex _17370) = (@ex _17370).
Proof. exact (eq_refl (@ex _17370)). Qed.
Lemma lem511530 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term171 _17370 _17371 P Q) = (term113 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511529 _17370) (@lem511528 _17370 _17371 P Q)). Qed.
Lemma lem511531 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem511532 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term172 _17370 _17371 P Q) = (term114 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511531) (@lem511530 _17370 _17371 P Q)). Qed.
Lemma lem511533 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term163 _17370 _17371 P Q) = (term163 _17370 _17371 P Q).
Proof. exact (eq_refl (term163 _17370 _17371 P Q)). Qed.
Lemma lem511534 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term167 _17370 _17371 P Q) = (term164 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511532 _17370 _17371 P Q) (@lem511533 _17370 _17371 P Q)). Qed.
Lemma lem511535 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem511536 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term173 _17370 _17371 P Q) = (term174 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511535) (@lem511534 _17370 _17371 P Q)). Qed.
Lemma lem511537 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term169 _17370 _17371 P Q y) = (term111 _17370 _17371 P Q y).
Proof. exact (eq_refl (term169 _17370 _17371 P Q y)). Qed.
Lemma lem511538 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem511539 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term175 _17370 _17371 P Q y) = (term176 _17370 _17371 P Q y).
Proof. exact (MK_COMB (@lem511538) (@lem511537 _17370 _17371 P Q y)). Qed.
Lemma lem511540 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term163 _17370 _17371 P Q) = (term163 _17370 _17371 P Q).
Proof. exact (eq_refl (term163 _17370 _17371 P Q)). Qed.
Lemma lem511541 {_17370 _17371 : Type'} (y : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term177 _17370 _17371 y P Q) = (term178 _17370 _17371 y P Q).
Proof. exact (MK_COMB (@lem511539 _17370 _17371 P Q y) (@lem511540 _17370 _17371 P Q)). Qed.
Lemma lem511542 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term179 _17370 _17371 P Q) = (term180 _17370 _17371 P Q).
Proof. exact (fun_ext (fun y : _17370 => @lem511541 _17370 _17371 y P Q)). Qed.
Lemma lem511543 {_17370 : Type'} : (@ex _17370) = (@ex _17370).
Proof. exact (eq_refl (@ex _17370)). Qed.
Lemma lem511544 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term168 _17370 _17371 P Q) = (term181 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511543 _17370) (@lem511542 _17370 _17371 P Q)). Qed.
Lemma lem511545 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : ((term167 _17370 _17371 P Q) = (term168 _17370 _17371 P Q)) = ((term164 _17370 _17371 P Q) = (term181 _17370 _17371 P Q)).
Proof. exact (MK_COMB (@lem511536 _17370 _17371 P Q) (@lem511544 _17370 _17371 P Q)). Qed.
Lemma lem511546 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term164 _17370 _17371 P Q) = (term181 _17370 _17371 P Q).
Proof. exact (EQ_MP (@lem511545 _17370 _17371 P Q) (@lem511526 _17370 _17371 P Q)). Qed.
Lemma lem511548 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term182 A P Q) = (term183 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem511549 {_17371 : Type'} (P : _17371 -> Prop) (Q : _17371 -> Prop) : (term182 _17371 P Q) = (term183 _17371 P Q).
Proof. exact (@lem511548 _17371 P Q). Qed.
Lemma lem511550 {_17370 _17371 : Type'} (y : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term184 _17370 _17371 y P Q) = (term185 _17370 _17371 y P Q).
Proof. exact (@lem511549 _17371 (term110 _17370 _17371 P Q y) (term162 _17370 _17371 P Q)). Qed.
Lemma lem511551 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term186 _17370 _17371 P Q y x) = (term108 _17370 _17371 P Q x y).
Proof. exact (eq_refl (term186 _17370 _17371 P Q y x)). Qed.
Lemma lem511552 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term187 _17370 _17371 P Q y) = (term110 _17370 _17371 P Q y).
Proof. exact (fun_ext (fun x : _17371 => @lem511551 _17370 _17371 P Q x y)). Qed.
Lemma lem511553 {_17371 : Type'} : (@ex _17371) = (@ex _17371).
Proof. exact (eq_refl (@ex _17371)). Qed.
Lemma lem511554 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term188 _17370 _17371 P Q y) = (term111 _17370 _17371 P Q y).
Proof. exact (MK_COMB (@lem511553 _17371) (@lem511552 _17370 _17371 P Q y)). Qed.
Lemma lem511555 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem511556 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term189 _17370 _17371 P Q y) = (term176 _17370 _17371 P Q y).
Proof. exact (MK_COMB (@lem511555) (@lem511554 _17370 _17371 P Q y)). Qed.
Lemma lem511557 {_17370 _17371 : Type'} (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term190 _17370 _17371 P Q x) = (term161 _17370 _17371 x P Q).
Proof. exact (eq_refl (term190 _17370 _17371 P Q x)). Qed.
Lemma lem511558 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term191 _17370 _17371 P Q) = (term162 _17370 _17371 P Q).
Proof. exact (fun_ext (fun x : _17371 => @lem511557 _17370 _17371 x P Q)). Qed.
Lemma lem511559 {_17371 : Type'} : (@ex _17371) = (@ex _17371).
Proof. exact (eq_refl (@ex _17371)). Qed.
Lemma lem511560 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term192 _17370 _17371 P Q) = (term163 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511559 _17371) (@lem511558 _17370 _17371 P Q)). Qed.
Lemma lem511561 {_17370 _17371 : Type'} (y : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term184 _17370 _17371 y P Q) = (term178 _17370 _17371 y P Q).
Proof. exact (MK_COMB (@lem511556 _17370 _17371 P Q y) (@lem511560 _17370 _17371 P Q)). Qed.
Lemma lem511562 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem511563 {_17370 _17371 : Type'} (y : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term193 _17370 _17371 y P Q) = (term194 _17370 _17371 y P Q).
Proof. exact (MK_COMB (@lem511562) (@lem511561 _17370 _17371 y P Q)). Qed.
Lemma lem511564 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term186 _17370 _17371 P Q y x) = (term108 _17370 _17371 P Q x y).
Proof. exact (eq_refl (term186 _17370 _17371 P Q y x)). Qed.
Lemma lem511565 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem511566 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term195 _17370 _17371 P Q y x) = (term196 _17370 _17371 P Q x y).
Proof. exact (MK_COMB (@lem511565) (@lem511564 _17370 _17371 P Q x y)). Qed.
Lemma lem511567 {_17370 _17371 : Type'} (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term190 _17370 _17371 P Q x) = (term161 _17370 _17371 x P Q).
Proof. exact (eq_refl (term190 _17370 _17371 P Q x)). Qed.
Lemma lem511568 {_17370 _17371 : Type'} (y : _17370) (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term197 _17370 _17371 y P Q x) = (term198 _17370 _17371 y x P Q).
Proof. exact (MK_COMB (@lem511566 _17370 _17371 P Q x y) (@lem511567 _17370 _17371 x P Q)). Qed.
Lemma lem511569 {_17370 _17371 : Type'} (y : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term199 _17370 _17371 y P Q) = (term200 _17370 _17371 y P Q).
Proof. exact (fun_ext (fun x : _17371 => @lem511568 _17370 _17371 y x P Q)). Qed.
Lemma lem511570 {_17371 : Type'} : (@ex _17371) = (@ex _17371).
Proof. exact (eq_refl (@ex _17371)). Qed.
Lemma lem511571 {_17370 _17371 : Type'} (y : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term185 _17370 _17371 y P Q) = (term201 _17370 _17371 y P Q).
Proof. exact (MK_COMB (@lem511570 _17371) (@lem511569 _17370 _17371 y P Q)). Qed.
Lemma lem511572 {_17370 _17371 : Type'} (y : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : ((term184 _17370 _17371 y P Q) = (term185 _17370 _17371 y P Q)) = ((term178 _17370 _17371 y P Q) = (term201 _17370 _17371 y P Q)).
Proof. exact (MK_COMB (@lem511563 _17370 _17371 y P Q) (@lem511571 _17370 _17371 y P Q)). Qed.
Lemma lem511573 {_17370 _17371 : Type'} (y : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term178 _17370 _17371 y P Q) = (term201 _17370 _17371 y P Q).
Proof. exact (EQ_MP (@lem511572 _17370 _17371 y P Q) (@lem511550 _17370 _17371 y P Q)). Qed.
Lemma lem511575 {A : Type'} (P : Prop) (Q : A -> Prop) : (term202 A P Q) = (term203 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem511576 {_17370 : Type'} (P : Prop) (Q : _17370 -> Prop) : (term202 _17370 P Q) = (term203 _17370 P Q).
Proof. exact (@lem511575 _17370 P Q). Qed.
Lemma lem511577 {_17370 _17371 : Type'} (y : _17370) (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term204 _17370 _17371 y x P Q) = (term205 _17370 _17371 y x P Q).
Proof. exact (@lem511576 _17370 (term108 _17370 _17371 P Q x y) (term160 _17370 _17371 x P Q)). Qed.
Lemma lem511578 {_17370 _17371 : Type'} (x : _17371) (y : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term206 _17370 _17371 x P Q y) = (term158 _17370 _17371 x y P Q).
Proof. exact (eq_refl (term206 _17370 _17371 x P Q y)). Qed.
Lemma lem511579 {_17370 _17371 : Type'} (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term207 _17370 _17371 x P Q) = (term160 _17370 _17371 x P Q).
Proof. exact (fun_ext (fun y : _17370 => @lem511578 _17370 _17371 x y P Q)). Qed.
Lemma lem511580 {_17370 : Type'} : (@ex _17370) = (@ex _17370).
Proof. exact (eq_refl (@ex _17370)). Qed.
Lemma lem511581 {_17370 _17371 : Type'} (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term208 _17370 _17371 x P Q) = (term161 _17370 _17371 x P Q).
Proof. exact (MK_COMB (@lem511580 _17370) (@lem511579 _17370 _17371 x P Q)). Qed.
Lemma lem511582 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term196 _17370 _17371 P Q x y) = (term196 _17370 _17371 P Q x y).
Proof. exact (eq_refl (term196 _17370 _17371 P Q x y)). Qed.
Lemma lem511583 {_17370 _17371 : Type'} (y : _17370) (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term204 _17370 _17371 y x P Q) = (term198 _17370 _17371 y x P Q).
Proof. exact (MK_COMB (@lem511582 _17370 _17371 P Q x y) (@lem511581 _17370 _17371 x P Q)). Qed.
Lemma lem511584 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem511585 {_17370 _17371 : Type'} (y : _17370) (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term209 _17370 _17371 y x P Q) = (term210 _17370 _17371 y x P Q).
Proof. exact (MK_COMB (@lem511584) (@lem511583 _17370 _17371 y x P Q)). Qed.
Lemma lem511586 {_17370 _17371 : Type'} (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term206 _17370 _17371 x P Q y') = (term158 _17370 _17371 x y' P Q).
Proof. exact (eq_refl (term206 _17370 _17371 x P Q y')). Qed.
Lemma lem511587 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term196 _17370 _17371 P Q x y) = (term196 _17370 _17371 P Q x y).
Proof. exact (eq_refl (term196 _17370 _17371 P Q x y)). Qed.
Lemma lem511588 {_17370 _17371 : Type'} (y : _17370) (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term211 _17370 _17371 y x P Q y') = (term212 _17370 _17371 y x y' P Q).
Proof. exact (MK_COMB (@lem511587 _17370 _17371 P Q x y) (@lem511586 _17370 _17371 x y' P Q)). Qed.
Lemma lem511589 {_17370 _17371 : Type'} (y : _17370) (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term213 _17370 _17371 y x P Q) = (term214 _17370 _17371 y x P Q).
Proof. exact (fun_ext (fun y' : _17370 => @lem511588 _17370 _17371 y x y' P Q)). Qed.
Lemma lem511590 {_17370 : Type'} : (@ex _17370) = (@ex _17370).
Proof. exact (eq_refl (@ex _17370)). Qed.
Lemma lem511591 {_17370 _17371 : Type'} (y : _17370) (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term205 _17370 _17371 y x P Q) = (term215 _17370 _17371 y x P Q).
Proof. exact (MK_COMB (@lem511590 _17370) (@lem511589 _17370 _17371 y x P Q)). Qed.
Lemma lem511592 {_17370 _17371 : Type'} (y : _17370) (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : ((term204 _17370 _17371 y x P Q) = (term205 _17370 _17371 y x P Q)) = ((term198 _17370 _17371 y x P Q) = (term215 _17370 _17371 y x P Q)).
Proof. exact (MK_COMB (@lem511585 _17370 _17371 y x P Q) (@lem511591 _17370 _17371 y x P Q)). Qed.
Lemma lem511593 {_17370 _17371 : Type'} (y : _17370) (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term198 _17370 _17371 y x P Q) = (term215 _17370 _17371 y x P Q).
Proof. exact (EQ_MP (@lem511592 _17370 _17371 y x P Q) (@lem511577 _17370 _17371 y x P Q)). Qed.
Lemma lem511594 {_17370 _17371 : Type'} (y : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term200 _17370 _17371 y P Q) = (term216 _17370 _17371 y P Q).
Proof. exact (fun_ext (fun x : _17371 => @lem511593 _17370 _17371 y x P Q)). Qed.
Lemma lem511595 {_17371 : Type'} : (@ex _17371) = (@ex _17371).
Proof. exact (eq_refl (@ex _17371)). Qed.
Lemma lem511596 {_17370 _17371 : Type'} (y : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term201 _17370 _17371 y P Q) = (term217 _17370 _17371 y P Q).
Proof. exact (MK_COMB (@lem511595 _17371) (@lem511594 _17370 _17371 y P Q)). Qed.
Lemma lem511597 {_17370 _17371 : Type'} (y : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term178 _17370 _17371 y P Q) = (term217 _17370 _17371 y P Q).
Proof. exact (TRANS (@lem511573 _17370 _17371 y P Q) (@lem511596 _17370 _17371 y P Q)). Qed.
Lemma lem511598 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term180 _17370 _17371 P Q) = (term218 _17370 _17371 P Q).
Proof. exact (fun_ext (fun y : _17370 => @lem511597 _17370 _17371 y P Q)). Qed.
Lemma lem511599 {_17370 : Type'} : (@ex _17370) = (@ex _17370).
Proof. exact (eq_refl (@ex _17370)). Qed.
Lemma lem511600 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term181 _17370 _17371 P Q) = (term219 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511599 _17370) (@lem511598 _17370 _17371 P Q)). Qed.
Lemma lem511601 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term164 _17370 _17371 P Q) = (term219 _17370 _17371 P Q).
Proof. exact (TRANS (@lem511546 _17370 _17371 P Q) (@lem511600 _17370 _17371 P Q)). Qed.
Lemma lem511603 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term85 _17370 _17371 P Q) = (term219 _17370 _17371 P Q).
Proof. exact (TRANS (@lem511520 _17370 _17371 P Q) (@lem511601 _17370 _17371 P Q)). Qed.
Lemma lem511604 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term0 _17370 _17371 P Q) = (term219 _17370 _17371 P Q).
Proof. exact (TRANS (@lem511224 _17370 _17371 P Q) (@lem511603 _17370 _17371 P Q)). Qed.
Lemma lem511605 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term0 _17370 _17371 P Q) : term219 _17370 _17371 P Q.
Proof. exact (EQ_MP (@lem511604 _17370 _17371 P Q) (@lem511133 _17370 _17371 P Q h1)). Qed.
Lemma lem511606 {_17370 _17371 : Type'} (y : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term217 _17370 _17371 y P Q) : term217 _17370 _17371 y P Q.
Proof. exact (h1). Qed.
Lemma lem511607 {_17370 _17371 : Type'} (y : _17370) (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term215 _17370 _17371 y x P Q) : term215 _17370 _17371 y x P Q.
Proof. exact (h1). Qed.
Lemma lem511608 {_17370 _17371 : Type'} (y : _17370) (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term212 _17370 _17371 y x y' P Q) : term212 _17370 _17371 y x y' P Q.
Proof. exact (h1). Qed.
Lemma lem511621 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term55 _17370 _17371 P Q x y) = (term55 _17370 _17371 P Q x y).
Proof. exact (eq_refl (term55 _17370 _17371 P Q x y)). Qed.
Lemma lem511622 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term63 _17370 _17371 P Q y) = (term63 _17370 _17371 P Q y).
Proof. exact (fun_ext (fun x : _17371 => @lem511621 _17370 _17371 P Q x y)). Qed.
Lemma lem511623 {_17371 : Type'} : (@all _17371) = (@all _17371).
Proof. exact (eq_refl (@all _17371)). Qed.
Lemma lem511624 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term64 _17370 _17371 P Q y) = (term64 _17370 _17371 P Q y).
Proof. exact (MK_COMB (@lem511623 _17371) (@lem511622 _17370 _17371 P Q y)). Qed.
Lemma lem511625 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term72 _17370 _17371 P Q) = (term72 _17370 _17371 P Q).
Proof. exact (fun_ext (fun y : _17370 => @lem511624 _17370 _17371 P Q y)). Qed.
Lemma lem511626 {_17370 : Type'} : (@all _17370) = (@all _17370).
Proof. exact (eq_refl (@all _17370)). Qed.
Lemma lem511627 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term73 _17370 _17371 P Q) = (term73 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511626 _17370) (@lem511625 _17370 _17371 P Q)). Qed.
Lemma lem511642 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y' : _17370) : (term156 _17370 _17371 P Q x y') = (term156 _17370 _17371 P Q x y').
Proof. exact (eq_refl (term156 _17370 _17371 P Q x y')). Qed.
Lemma lem511643 {_17370 _17371 : Type'} (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term158 _17370 _17371 x y' P Q) = (term158 _17370 _17371 x y' P Q).
Proof. exact (MK_COMB (@lem511642 _17370 _17371 P Q x y') (@lem511627 _17370 _17371 P Q)). Qed.
Lemma lem511656 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term54 _17370 _17371 P Q x y) = (term54 _17370 _17371 P Q x y).
Proof. exact (eq_refl (term54 _17370 _17371 P Q x y)). Qed.
Lemma lem511661 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (Q x y) = (Q x y).
Proof. exact (eq_refl (Q x y)). Qed.
Lemma lem511662 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) : (term21 _17370 _17371 Q x) = (term21 _17370 _17371 Q x).
Proof. exact (fun_ext (fun y : _17370 => @lem511661 _17370 _17371 Q x y)). Qed.
Lemma lem511663 {_17370 : Type'} : (@all _17370) = (@all _17370).
Proof. exact (eq_refl (@all _17370)). Qed.
Lemma lem511664 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) : (term22 _17370 _17371 Q x) = (term22 _17370 _17371 Q x).
Proof. exact (MK_COMB (@lem511663 _17370) (@lem511662 _17370 _17371 Q x)). Qed.
Lemma lem511671 {_17371 : Type'} (P : _17371 -> Prop) (x : _17371) : (term42 _17371 P x) = (term42 _17371 P x).
Proof. exact (eq_refl (term42 _17371 P x)). Qed.
Lemma lem511672 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term43 _17370 _17371 P Q x) = (term43 _17370 _17371 P Q x).
Proof. exact (MK_COMB (@lem511671 _17371 P x) (@lem511664 _17370 _17371 Q x)). Qed.
Lemma lem511673 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term51 _17370 _17371 P Q) = (term51 _17370 _17371 P Q).
Proof. exact (fun_ext (fun x : _17371 => @lem511672 _17370 _17371 P Q x)). Qed.
Lemma lem511674 {_17371 : Type'} : (@all _17371) = (@all _17371).
Proof. exact (eq_refl (@all _17371)). Qed.
Lemma lem511675 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term52 _17370 _17371 P Q) = (term52 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511674 _17371) (@lem511673 _17370 _17371 P Q)). Qed.
Lemma lem511676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem511677 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term79 _17370 _17371 P Q) = (term79 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511676) (@lem511675 _17370 _17371 P Q)). Qed.
Lemma lem511678 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term108 _17370 _17371 P Q x y) = (term108 _17370 _17371 P Q x y).
Proof. exact (MK_COMB (@lem511677 _17370 _17371 P Q) (@lem511656 _17370 _17371 P Q x y)). Qed.
Lemma lem511679 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem511680 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term196 _17370 _17371 P Q x y) = (term196 _17370 _17371 P Q x y).
Proof. exact (MK_COMB (@lem511679) (@lem511678 _17370 _17371 P Q x y)). Qed.
Lemma lem511681 {_17370 _17371 : Type'} (y : _17370) (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term212 _17370 _17371 y x y' P Q) = (term212 _17370 _17371 y x y' P Q).
Proof. exact (MK_COMB (@lem511680 _17370 _17371 P Q x y) (@lem511643 _17370 _17371 x y' P Q)). Qed.
Lemma lem511682 {_17370 _17371 : Type'} (y : _17370) (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term212 _17370 _17371 y x y' P Q) : term212 _17370 _17371 y x y' P Q.
Proof. exact (EQ_MP (@lem511681 _17370 _17371 y x y' P Q) (@lem511608 _17370 _17371 y x y' P Q h1)). Qed.
Lemma lem511683 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : term108 _17370 _17371 P Q x y.
Proof. exact (h1). Qed.
Lemma lem511684 {_17370 _17371 : Type'} (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : term158 _17370 _17371 x y' P Q.
Proof. exact (h1). Qed.
Lemma lem511685 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : term54 _17370 _17371 P Q x y.
Proof. exact (proj2 (@lem511683 _17370 _17371 P Q x y h1)). Qed.
Lemma lem511686 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : term52 _17370 _17371 P Q.
Proof. exact (proj1 (@lem511683 _17370 _17371 P Q x y h1)). Qed.
Lemma lem511689 {_17370 _17371 : Type'} (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : term73 _17370 _17371 P Q.
Proof. exact (proj2 (@lem511684 _17370 _17371 x y' P Q h1)). Qed.
Lemma lem511690 {_17370 _17371 : Type'} (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : term54 _17370 _17371 P Q x y'.
Proof. exact (proj1 (@lem511684 _17370 _17371 x y' P Q h1)). Qed.
Lemma lem511694 {A : Type'} (P : Prop) (Q : A -> Prop) : (term220 A P Q) = (term221 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem511695 {_17370 : Type'} (P : Prop) (Q : _17370 -> Prop) : (term220 _17370 P Q) = (term221 _17370 P Q).
Proof. exact (@lem511694 _17370 P Q). Qed.
Lemma lem511696 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term222 _17370 _17371 P Q x) = (term223 _17370 _17371 P Q x).
Proof. exact (@lem511695 _17370 (term224 _17371 P x) (term21 _17370 _17371 Q x)). Qed.
Lemma lem511697 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term32 _17370 _17371 Q x y) = (Q x y).
Proof. exact (eq_refl (term32 _17370 _17371 Q x y)). Qed.
Lemma lem511698 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) : (term225 _17370 _17371 Q x) = (term21 _17370 _17371 Q x).
Proof. exact (fun_ext (fun y : _17370 => @lem511697 _17370 _17371 Q x y)). Qed.
Lemma lem511699 {_17370 : Type'} : (@all _17370) = (@all _17370).
Proof. exact (eq_refl (@all _17370)). Qed.
Lemma lem511700 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) : (term226 _17370 _17371 Q x) = (term22 _17370 _17371 Q x).
Proof. exact (MK_COMB (@lem511699 _17370) (@lem511698 _17370 _17371 Q x)). Qed.
Lemma lem511701 {_17371 : Type'} (P : _17371 -> Prop) (x : _17371) : (term42 _17371 P x) = (term42 _17371 P x).
Proof. exact (eq_refl (term42 _17371 P x)). Qed.
Lemma lem511702 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term222 _17370 _17371 P Q x) = (term43 _17370 _17371 P Q x).
Proof. exact (MK_COMB (@lem511701 _17371 P x) (@lem511700 _17370 _17371 Q x)). Qed.
Lemma lem511703 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem511704 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term227 _17370 _17371 P Q x) = (term228 _17370 _17371 P Q x).
Proof. exact (MK_COMB (@lem511703) (@lem511702 _17370 _17371 P Q x)). Qed.
Lemma lem511705 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term32 _17370 _17371 Q x y) = (Q x y).
Proof. exact (eq_refl (term32 _17370 _17371 Q x y)). Qed.
Lemma lem511706 {_17371 : Type'} (P : _17371 -> Prop) (x : _17371) : (term42 _17371 P x) = (term42 _17371 P x).
Proof. exact (eq_refl (term42 _17371 P x)). Qed.
Lemma lem511707 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term229 _17370 _17371 P Q x y) = (term55 _17370 _17371 P Q x y).
Proof. exact (MK_COMB (@lem511706 _17371 P x) (@lem511705 _17370 _17371 Q x y)). Qed.
Lemma lem511708 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term230 _17370 _17371 P Q x) = (term231 _17370 _17371 P Q x).
Proof. exact (fun_ext (fun y : _17370 => @lem511707 _17370 _17371 P Q x y)). Qed.
Lemma lem511709 {_17370 : Type'} : (@all _17370) = (@all _17370).
Proof. exact (eq_refl (@all _17370)). Qed.
Lemma lem511710 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term223 _17370 _17371 P Q x) = (term232 _17370 _17371 P Q x).
Proof. exact (MK_COMB (@lem511709 _17370) (@lem511708 _17370 _17371 P Q x)). Qed.
Lemma lem511711 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : ((term222 _17370 _17371 P Q x) = (term223 _17370 _17371 P Q x)) = ((term43 _17370 _17371 P Q x) = (term232 _17370 _17371 P Q x)).
Proof. exact (MK_COMB (@lem511704 _17370 _17371 P Q x) (@lem511710 _17370 _17371 P Q x)). Qed.
Lemma lem511712 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term43 _17370 _17371 P Q x) = (term232 _17370 _17371 P Q x).
Proof. exact (EQ_MP (@lem511711 _17370 _17371 P Q x) (@lem511696 _17370 _17371 P Q x)). Qed.
Lemma lem511713 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term51 _17370 _17371 P Q) = (term233 _17370 _17371 P Q).
Proof. exact (fun_ext (fun x : _17371 => @lem511712 _17370 _17371 P Q x)). Qed.
Lemma lem511714 {_17371 : Type'} : (@all _17371) = (@all _17371).
Proof. exact (eq_refl (@all _17371)). Qed.
Lemma lem511715 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term52 _17370 _17371 P Q) = (term234 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511714 _17371) (@lem511713 _17370 _17371 P Q)). Qed.
Lemma lem511722 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term55 _17370 _17371 P Q x y) = (term55 _17370 _17371 P Q x y).
Proof. exact (eq_refl (term55 _17370 _17371 P Q x y)). Qed.
Lemma lem511723 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term231 _17370 _17371 P Q x) = (term231 _17370 _17371 P Q x).
Proof. exact (fun_ext (fun y : _17370 => @lem511722 _17370 _17371 P Q x y)). Qed.
Lemma lem511724 {_17370 : Type'} : (@all _17370) = (@all _17370).
Proof. exact (eq_refl (@all _17370)). Qed.
Lemma lem511725 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) : (term232 _17370 _17371 P Q x) = (term232 _17370 _17371 P Q x).
Proof. exact (MK_COMB (@lem511724 _17370) (@lem511723 _17370 _17371 P Q x)). Qed.
Lemma lem511726 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term233 _17370 _17371 P Q) = (term233 _17370 _17371 P Q).
Proof. exact (fun_ext (fun x : _17371 => @lem511725 _17370 _17371 P Q x)). Qed.
Lemma lem511727 {_17371 : Type'} : (@all _17371) = (@all _17371).
Proof. exact (eq_refl (@all _17371)). Qed.
Lemma lem511728 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term234 _17370 _17371 P Q) = (term234 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511727 _17371) (@lem511726 _17370 _17371 P Q)). Qed.
Lemma lem511729 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term52 _17370 _17371 P Q) = (term234 _17370 _17371 P Q).
Proof. exact (TRANS (@lem511715 _17370 _17371 P Q) (@lem511728 _17370 _17371 P Q)). Qed.
Lemma lem511730 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : term234 _17370 _17371 P Q.
Proof. exact (EQ_MP (@lem511729 _17370 _17371 P Q) (@lem511686 _17370 _17371 P Q x y h1)). Qed.
Lemma lem511746 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term55 _17370 _17371 P Q x y) = (term55 _17370 _17371 P Q x y).
Proof. exact (eq_refl (term55 _17370 _17371 P Q x y)). Qed.
Lemma lem511747 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term63 _17370 _17371 P Q y) = (term63 _17370 _17371 P Q y).
Proof. exact (fun_ext (fun x : _17371 => @lem511746 _17370 _17371 P Q x y)). Qed.
Lemma lem511748 {_17371 : Type'} : (@all _17371) = (@all _17371).
Proof. exact (eq_refl (@all _17371)). Qed.
Lemma lem511749 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (y : _17370) : (term64 _17370 _17371 P Q y) = (term64 _17370 _17371 P Q y).
Proof. exact (MK_COMB (@lem511748 _17371) (@lem511747 _17370 _17371 P Q y)). Qed.
Lemma lem511750 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term72 _17370 _17371 P Q) = (term72 _17370 _17371 P Q).
Proof. exact (fun_ext (fun y : _17370 => @lem511749 _17370 _17371 P Q y)). Qed.
Lemma lem511751 {_17370 : Type'} : (@all _17370) = (@all _17370).
Proof. exact (eq_refl (@all _17370)). Qed.
Lemma lem511753 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term73 _17370 _17371 P Q) = (term73 _17370 _17371 P Q).
Proof. exact (MK_COMB (@lem511751 _17370) (@lem511750 _17370 _17371 P Q)). Qed.
Lemma lem511754 {_17370 _17371 : Type'} (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : term73 _17370 _17371 P Q.
Proof. exact (EQ_MP (@lem511753 _17370 _17371 P Q) (@lem511689 _17370 _17371 x y' P Q h1)). Qed.
Lemma lem511763 {_17370 _17371 : Type'} (_10676 : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : term235 _17370 _17371 P Q _10676.
Proof. exact (@lem511730 _17370 _17371 P Q x y h1 _10676). Qed.
Lemma lem511764 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (_10676 : _17371) : (term235 _17370 _17371 P Q _10676) = (term232 _17370 _17371 P Q _10676).
Proof. exact (eq_refl (term235 _17370 _17371 P Q _10676)). Qed.
Lemma lem511765 {_17370 _17371 : Type'} (_10676 : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : term232 _17370 _17371 P Q _10676.
Proof. exact (EQ_MP (@lem511764 _17370 _17371 P Q _10676) (@lem511763 _17370 _17371 _10676 P Q x y h1)). Qed.
Lemma lem511766 {_17370 _17371 : Type'} (_10676 : _17371) (_10677 : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : term236 _17370 _17371 P Q _10676 _10677.
Proof. exact (@lem511765 _17370 _17371 _10676 P Q x y h1 _10677). Qed.
Lemma lem511767 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (_10676 : _17371) (_10677 : _17370) : (term236 _17370 _17371 P Q _10676 _10677) = (term55 _17370 _17371 P Q _10676 _10677).
Proof. exact (eq_refl (term236 _17370 _17371 P Q _10676 _10677)). Qed.
Lemma lem511769 {_17370 _17371 : Type'} (_10678 : _17370) (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : term237 _17370 _17371 P Q _10678.
Proof. exact (@lem511754 _17370 _17371 x y' P Q h1 _10678). Qed.
Lemma lem511770 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (_10678 : _17370) : (term237 _17370 _17371 P Q _10678) = (term64 _17370 _17371 P Q _10678).
Proof. exact (eq_refl (term237 _17370 _17371 P Q _10678)). Qed.
Lemma lem511771 {_17370 _17371 : Type'} (_10678 : _17370) (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : term64 _17370 _17371 P Q _10678.
Proof. exact (EQ_MP (@lem511770 _17370 _17371 P Q _10678) (@lem511769 _17370 _17371 _10678 x y' P Q h1)). Qed.
Lemma lem511772 {_17370 _17371 : Type'} (_10678 : _17370) (_10679 : _17371) (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : term238 _17370 _17371 P Q _10678 _10679.
Proof. exact (@lem511771 _17370 _17371 _10678 x y' P Q h1 _10679). Qed.
Lemma lem511773 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (_10679 : _17371) (_10678 : _17370) : (term238 _17370 _17371 P Q _10678 _10679) = (term55 _17370 _17371 P Q _10679 _10678).
Proof. exact (eq_refl (term238 _17370 _17371 P Q _10678 _10679)). Qed.
Lemma lem511780 {_17370 _17371 : Type'} (_10676 : _17371) (_10677 : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : term55 _17370 _17371 P Q _10676 _10677.
Proof. exact (EQ_MP (@lem511767 _17370 _17371 P Q _10676 _10677) (@lem511766 _17370 _17371 _10676 _10677 P Q x y h1)). Qed.
Lemma lem511784 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : term34 _17370 _17371 Q x y.
Proof. exact (proj2 (@lem511685 _17370 _17371 P Q x y h1)). Qed.
Lemma lem511790 {_17370 _17371 : Type'} (_10679 : _17371) (_10678 : _17370) (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : term55 _17370 _17371 P Q _10679 _10678.
Proof. exact (EQ_MP (@lem511773 _17370 _17371 P Q _10679 _10678) (@lem511772 _17370 _17371 _10678 _10679 x y' P Q h1)). Qed.
Lemma lem511794 {_17370 _17371 : Type'} (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : term34 _17370 _17371 Q x y'.
Proof. exact (proj2 (@lem511690 _17370 _17371 x y' P Q h1)). Qed.
Lemma lem511796 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : P x.
Proof. exact (proj1 (@lem511685 _17370 _17371 P Q x y h1)). Qed.
Lemma lem511797 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : term239 _17371 P x.
Proof. exact (fun h0 : term224 _17371 P x => @lem511796 _17370 _17371 P Q x y h1). Qed.
Lemma lem511799 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem511800 {_17371 : Type'} (P : _17371 -> Prop) (x : _17371) : (term239 _17371 P x) = (P x).
Proof. exact (@lem511799 (P x)). Qed.
Lemma lem511801 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : P x.
Proof. exact (EQ_MP (@lem511800 _17371 P x) (@lem511797 _17370 _17371 P Q x y h1)). Qed.
Lemma lem511807 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem511808 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10677 : _17370) (P : _17371 -> Prop) (_10676 : _17371) : (term55 _17370 _17371 P Q _10676 _10677) = (term241 _17370 _17371 Q _10677 P _10676).
Proof. exact (@lem511807 (Q _10676 _10677) (term224 _17371 P _10676)). Qed.
Lemma lem511814 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem511815 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10677 : _17370) (P : _17371 -> Prop) (_10676 : _17371) : (term242 _17370 _17371 P Q _10676 _10677) = (term243 _17370 _17371 Q _10677 P _10676).
Proof. exact (MK_COMB (@lem511814) (@lem511808 _17370 _17371 Q _10677 P _10676)). Qed.
Lemma lem511821 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10677 : _17370) (P : _17371 -> Prop) (_10676 : _17371) : (term241 _17370 _17371 Q _10677 P _10676) = (term241 _17370 _17371 Q _10677 P _10676).
Proof. exact (eq_refl (term241 _17370 _17371 Q _10677 P _10676)). Qed.
Lemma lem511822 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10677 : _17370) (P : _17371 -> Prop) (_10676 : _17371) : ((term55 _17370 _17371 P Q _10676 _10677) = (term241 _17370 _17371 Q _10677 P _10676)) = ((term241 _17370 _17371 Q _10677 P _10676) = (term241 _17370 _17371 Q _10677 P _10676)).
Proof. exact (MK_COMB (@lem511815 _17370 _17371 Q _10677 P _10676) (@lem511821 _17370 _17371 Q _10677 P _10676)). Qed.
Lemma lem511824 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem511825 (x : Prop) : (x = x) = True.
Proof. exact (@lem511824 Prop x). Qed.
Lemma lem511826 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10677 : _17370) (P : _17371 -> Prop) (_10676 : _17371) : ((term241 _17370 _17371 Q _10677 P _10676) = (term241 _17370 _17371 Q _10677 P _10676)) = True.
Proof. exact (@lem511825 (term241 _17370 _17371 Q _10677 P _10676)). Qed.
Lemma lem511827 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10677 : _17370) (P : _17371 -> Prop) (_10676 : _17371) : ((term55 _17370 _17371 P Q _10676 _10677) = (term241 _17370 _17371 Q _10677 P _10676)) = True.
Proof. exact (TRANS (@lem511822 _17370 _17371 Q _10677 P _10676) (@lem511826 _17370 _17371 Q _10677 P _10676)). Qed.
Lemma lem511828 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10677 : _17370) (P : _17371 -> Prop) (_10676 : _17371) : True = ((term55 _17370 _17371 P Q _10676 _10677) = (term241 _17370 _17371 Q _10677 P _10676)).
Proof. exact (SYM (@lem511827 _17370 _17371 Q _10677 P _10676)). Qed.
Lemma lem511829 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10677 : _17370) (P : _17371 -> Prop) (_10676 : _17371) : (term55 _17370 _17371 P Q _10676 _10677) = (term241 _17370 _17371 Q _10677 P _10676).
Proof. exact (EQ_MP (@lem511828 _17370 _17371 Q _10677 P _10676) (@lem0)). Qed.
Lemma lem511830 {_17370 _17371 : Type'} (_10677 : _17370) (_10676 : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : term241 _17370 _17371 Q _10677 P _10676.
Proof. exact (EQ_MP (@lem511829 _17370 _17371 Q _10677 P _10676) (@lem511780 _17370 _17371 _10676 _10677 P Q x y h1)). Qed.
Lemma lem511832 (b : Prop) (a : Prop) : (a \/ b) = (term244 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem511833 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (_10676 : _17371) (_10677 : _17370) : (term241 _17370 _17371 Q _10677 P _10676) = (term245 _17370 _17371 P Q _10676 _10677).
Proof. exact (@lem511832 (term224 _17371 P _10676) (Q _10676 _10677)). Qed.
Lemma lem511835 (a : Prop) : (term6 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem511836 {_17371 : Type'} (P : _17371 -> Prop) (_10676 : _17371) : (term246 _17371 P _10676) = (P _10676).
Proof. exact (@lem511835 (P _10676)). Qed.
Lemma lem511837 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem511838 {_17371 : Type'} (P : _17371 -> Prop) (_10676 : _17371) : (term247 _17371 P _10676) = (term23 _17371 P _10676).
Proof. exact (MK_COMB (@lem511837) (@lem511836 _17371 P _10676)). Qed.
Lemma lem511839 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10676 : _17371) (_10677 : _17370) : (Q _10676 _10677) = (Q _10676 _10677).
Proof. exact (eq_refl (Q _10676 _10677)). Qed.
Lemma lem511840 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (_10676 : _17371) (_10677 : _17370) : (term245 _17370 _17371 P Q _10676 _10677) = (term17 _17370 _17371 P Q _10676 _10677).
Proof. exact (MK_COMB (@lem511838 _17371 P _10676) (@lem511839 _17370 _17371 Q _10676 _10677)). Qed.
Lemma lem511841 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (_10676 : _17371) (_10677 : _17370) : (term241 _17370 _17371 Q _10677 P _10676) = (term17 _17370 _17371 P Q _10676 _10677).
Proof. exact (TRANS (@lem511833 _17370 _17371 P Q _10676 _10677) (@lem511840 _17370 _17371 P Q _10676 _10677)). Qed.
Lemma lem511844 {_17370 _17371 : Type'} (_10676 : _17371) (_10677 : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : term17 _17370 _17371 P Q _10676 _10677.
Proof. exact (EQ_MP (@lem511841 _17370 _17371 P Q _10676 _10677) (@lem511830 _17370 _17371 _10677 _10676 P Q x y h1)). Qed.
Lemma lem511845 {_17370 _17371 : Type'} (_10676 : _17371) (_10677 : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : term17 _17370 _17371 P Q _10676 _10677.
Proof. exact (@lem511844 _17370 _17371 _10676 _10677 P Q x y h1). Qed.
Lemma lem511846 {_17370 _17371 : Type'} (_10677 : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : term17 _17370 _17371 P Q x _10677.
Proof. exact (@lem511845 _17370 _17371 x _10677 P Q x y h1). Qed.
Lemma lem511849 {_17370 _17371 : Type'} (_10677 : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : Q x _10677.
Proof. exact (@lem511846 _17370 _17371 _10677 P Q x y h1 (@lem511801 _17370 _17371 P Q x y h1)). Qed.
Lemma lem511850 {_17370 _17371 : Type'} (_10677 : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : Q x _10677.
Proof. exact (@lem511849 _17370 _17371 _10677 P Q x y h1). Qed.
Lemma lem511851 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : Q x y.
Proof. exact (@lem511850 _17370 _17371 y P Q x y h1). Qed.
Lemma lem511852 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : term248 _17370 _17371 Q x y.
Proof. exact (fun h0 : term34 _17370 _17371 Q x y => @lem511851 _17370 _17371 P Q x y h1). Qed.
Lemma lem511854 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem511855 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term248 _17370 _17371 Q x y) = (Q x y).
Proof. exact (@lem511854 (Q x y)). Qed.
Lemma lem511856 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : Q x y.
Proof. exact (EQ_MP (@lem511855 _17370 _17371 Q x y) (@lem511852 _17370 _17371 P Q x y h1)). Qed.
Lemma lem511859 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem511861 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) : (term34 _17370 _17371 Q x y) = (term249 _17370 _17371 Q x y).
Proof. exact (@lem511859 (Q x y)). Qed.
Lemma lem511864 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : term249 _17370 _17371 Q x y.
Proof. exact (EQ_MP (@lem511861 _17370 _17371 Q x y) (@lem511784 _17370 _17371 P Q x y h1)). Qed.
Lemma lem511867 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : False.
Proof. exact (@lem511864 _17370 _17371 P Q x y h1 (@lem511856 _17370 _17371 P Q x y h1)). Qed.
Lemma lem511868 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : term250.
Proof. exact (fun h0 : ~ False => @lem511867 _17370 _17371 P Q x y h1). Qed.
Lemma lem511870 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem511871 : term250 = False.
Proof. exact (@lem511870 False). Qed.
Lemma lem511872 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (x : _17371) (y : _17370) (h1 : term108 _17370 _17371 P Q x y) : False.
Proof. exact (EQ_MP (@lem511871) (@lem511868 _17370 _17371 P Q x y h1)). Qed.
Lemma lem511874 {_17370 _17371 : Type'} (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : P x.
Proof. exact (proj1 (@lem511690 _17370 _17371 x y' P Q h1)). Qed.
Lemma lem511875 {_17370 _17371 : Type'} (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : term239 _17371 P x.
Proof. exact (fun h0 : term224 _17371 P x => @lem511874 _17370 _17371 x y' P Q h1). Qed.
Lemma lem511877 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem511878 {_17371 : Type'} (P : _17371 -> Prop) (x : _17371) : (term239 _17371 P x) = (P x).
Proof. exact (@lem511877 (P x)). Qed.
Lemma lem511879 {_17370 _17371 : Type'} (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : P x.
Proof. exact (EQ_MP (@lem511878 _17371 P x) (@lem511875 _17370 _17371 x y' P Q h1)). Qed.
Lemma lem511885 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem511886 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10678 : _17370) (P : _17371 -> Prop) (_10679 : _17371) : (term55 _17370 _17371 P Q _10679 _10678) = (term241 _17370 _17371 Q _10678 P _10679).
Proof. exact (@lem511885 (Q _10679 _10678) (term224 _17371 P _10679)). Qed.
Lemma lem511892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem511893 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10678 : _17370) (P : _17371 -> Prop) (_10679 : _17371) : (term242 _17370 _17371 P Q _10679 _10678) = (term243 _17370 _17371 Q _10678 P _10679).
Proof. exact (MK_COMB (@lem511892) (@lem511886 _17370 _17371 Q _10678 P _10679)). Qed.
Lemma lem511899 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10678 : _17370) (P : _17371 -> Prop) (_10679 : _17371) : (term241 _17370 _17371 Q _10678 P _10679) = (term241 _17370 _17371 Q _10678 P _10679).
Proof. exact (eq_refl (term241 _17370 _17371 Q _10678 P _10679)). Qed.
Lemma lem511900 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10678 : _17370) (P : _17371 -> Prop) (_10679 : _17371) : ((term55 _17370 _17371 P Q _10679 _10678) = (term241 _17370 _17371 Q _10678 P _10679)) = ((term241 _17370 _17371 Q _10678 P _10679) = (term241 _17370 _17371 Q _10678 P _10679)).
Proof. exact (MK_COMB (@lem511893 _17370 _17371 Q _10678 P _10679) (@lem511899 _17370 _17371 Q _10678 P _10679)). Qed.
Lemma lem511902 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem511903 (x : Prop) : (x = x) = True.
Proof. exact (@lem511902 Prop x). Qed.
Lemma lem511904 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10678 : _17370) (P : _17371 -> Prop) (_10679 : _17371) : ((term241 _17370 _17371 Q _10678 P _10679) = (term241 _17370 _17371 Q _10678 P _10679)) = True.
Proof. exact (@lem511903 (term241 _17370 _17371 Q _10678 P _10679)). Qed.
Lemma lem511905 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10678 : _17370) (P : _17371 -> Prop) (_10679 : _17371) : ((term55 _17370 _17371 P Q _10679 _10678) = (term241 _17370 _17371 Q _10678 P _10679)) = True.
Proof. exact (TRANS (@lem511900 _17370 _17371 Q _10678 P _10679) (@lem511904 _17370 _17371 Q _10678 P _10679)). Qed.
Lemma lem511906 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10678 : _17370) (P : _17371 -> Prop) (_10679 : _17371) : True = ((term55 _17370 _17371 P Q _10679 _10678) = (term241 _17370 _17371 Q _10678 P _10679)).
Proof. exact (SYM (@lem511905 _17370 _17371 Q _10678 P _10679)). Qed.
Lemma lem511907 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10678 : _17370) (P : _17371 -> Prop) (_10679 : _17371) : (term55 _17370 _17371 P Q _10679 _10678) = (term241 _17370 _17371 Q _10678 P _10679).
Proof. exact (EQ_MP (@lem511906 _17370 _17371 Q _10678 P _10679) (@lem0)). Qed.
Lemma lem511908 {_17370 _17371 : Type'} (_10678 : _17370) (_10679 : _17371) (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : term241 _17370 _17371 Q _10678 P _10679.
Proof. exact (EQ_MP (@lem511907 _17370 _17371 Q _10678 P _10679) (@lem511790 _17370 _17371 _10679 _10678 x y' P Q h1)). Qed.
Lemma lem511910 (b : Prop) (a : Prop) : (a \/ b) = (term244 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem511911 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (_10679 : _17371) (_10678 : _17370) : (term241 _17370 _17371 Q _10678 P _10679) = (term245 _17370 _17371 P Q _10679 _10678).
Proof. exact (@lem511910 (term224 _17371 P _10679) (Q _10679 _10678)). Qed.
Lemma lem511913 (a : Prop) : (term6 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem511914 {_17371 : Type'} (P : _17371 -> Prop) (_10679 : _17371) : (term246 _17371 P _10679) = (P _10679).
Proof. exact (@lem511913 (P _10679)). Qed.
Lemma lem511915 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem511916 {_17371 : Type'} (P : _17371 -> Prop) (_10679 : _17371) : (term247 _17371 P _10679) = (term23 _17371 P _10679).
Proof. exact (MK_COMB (@lem511915) (@lem511914 _17371 P _10679)). Qed.
Lemma lem511917 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (_10679 : _17371) (_10678 : _17370) : (Q _10679 _10678) = (Q _10679 _10678).
Proof. exact (eq_refl (Q _10679 _10678)). Qed.
Lemma lem511918 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (_10679 : _17371) (_10678 : _17370) : (term245 _17370 _17371 P Q _10679 _10678) = (term17 _17370 _17371 P Q _10679 _10678).
Proof. exact (MK_COMB (@lem511916 _17371 P _10679) (@lem511917 _17370 _17371 Q _10679 _10678)). Qed.
Lemma lem511919 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (_10679 : _17371) (_10678 : _17370) : (term241 _17370 _17371 Q _10678 P _10679) = (term17 _17370 _17371 P Q _10679 _10678).
Proof. exact (TRANS (@lem511911 _17370 _17371 P Q _10679 _10678) (@lem511918 _17370 _17371 P Q _10679 _10678)). Qed.
Lemma lem511922 {_17370 _17371 : Type'} (_10679 : _17371) (_10678 : _17370) (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : term17 _17370 _17371 P Q _10679 _10678.
Proof. exact (EQ_MP (@lem511919 _17370 _17371 P Q _10679 _10678) (@lem511908 _17370 _17371 _10678 _10679 x y' P Q h1)). Qed.
Lemma lem511923 {_17370 _17371 : Type'} (_10679 : _17371) (_10678 : _17370) (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : term17 _17370 _17371 P Q _10679 _10678.
Proof. exact (@lem511922 _17370 _17371 _10679 _10678 x y' P Q h1). Qed.
Lemma lem511924 {_17370 _17371 : Type'} (_10678 : _17370) (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : term17 _17370 _17371 P Q x _10678.
Proof. exact (@lem511923 _17370 _17371 x _10678 x y' P Q h1). Qed.
Lemma lem511927 {_17370 _17371 : Type'} (_10678 : _17370) (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : Q x _10678.
Proof. exact (@lem511924 _17370 _17371 _10678 x y' P Q h1 (@lem511879 _17370 _17371 x y' P Q h1)). Qed.
Lemma lem511928 {_17370 _17371 : Type'} (_10678 : _17370) (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : Q x _10678.
Proof. exact (@lem511927 _17370 _17371 _10678 x y' P Q h1). Qed.
Lemma lem511929 {_17370 _17371 : Type'} (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : Q x y'.
Proof. exact (@lem511928 _17370 _17371 y' x y' P Q h1). Qed.
Lemma lem511930 {_17370 _17371 : Type'} (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : term248 _17370 _17371 Q x y'.
Proof. exact (fun h0 : term34 _17370 _17371 Q x y' => @lem511929 _17370 _17371 x y' P Q h1). Qed.
Lemma lem511932 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem511933 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) (y' : _17370) : (term248 _17370 _17371 Q x y') = (Q x y').
Proof. exact (@lem511932 (Q x y')). Qed.
Lemma lem511934 {_17370 _17371 : Type'} (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : Q x y'.
Proof. exact (EQ_MP (@lem511933 _17370 _17371 Q x y') (@lem511930 _17370 _17371 x y' P Q h1)). Qed.
Lemma lem511937 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem511939 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (x : _17371) (y' : _17370) : (term34 _17370 _17371 Q x y') = (term249 _17370 _17371 Q x y').
Proof. exact (@lem511937 (Q x y')). Qed.
Lemma lem511942 {_17370 _17371 : Type'} (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : term249 _17370 _17371 Q x y'.
Proof. exact (EQ_MP (@lem511939 _17370 _17371 Q x y') (@lem511794 _17370 _17371 x y' P Q h1)). Qed.
Lemma lem511945 {_17370 _17371 : Type'} (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : False.
Proof. exact (@lem511942 _17370 _17371 x y' P Q h1 (@lem511934 _17370 _17371 x y' P Q h1)). Qed.
Lemma lem511946 {_17370 _17371 : Type'} (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : term250.
Proof. exact (fun h0 : ~ False => @lem511945 _17370 _17371 x y' P Q h1). Qed.
Lemma lem511948 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem511949 : term250 = False.
Proof. exact (@lem511948 False). Qed.
Lemma lem511950 {_17370 _17371 : Type'} (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term158 _17370 _17371 x y' P Q) : False.
Proof. exact (EQ_MP (@lem511949) (@lem511946 _17370 _17371 x y' P Q h1)). Qed.
Lemma lem511951 {_17370 _17371 : Type'} (y : _17370) (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term212 _17370 _17371 y x y' P Q) : False.
Proof. exact (or_elim (@lem511682 _17370 _17371 y x y' P Q h1) (fun h0 : term108 _17370 _17371 P Q x y => @lem511872 _17370 _17371 P Q x y h0) (fun h0 : term158 _17370 _17371 x y' P Q => @lem511950 _17370 _17371 x y' P Q h0)). Qed.
Lemma lem511952 {_17370 _17371 : Type'} (y : _17370) (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term212 _17370 _17371 y x y' P Q) : (term212 _17370 _17371 y x y' P Q) = False.
Proof. exact (prop_ext (fun h2 : term212 _17370 _17371 y x y' P Q => @lem511951 _17370 _17371 y x y' P Q h1) (fun h2 : False => @lem511682 _17370 _17371 y x y' P Q h1)). Qed.
Lemma lem511953 {_17370 _17371 : Type'} (y : _17370) (x : _17371) (y' : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term212 _17370 _17371 y x y' P Q) : False.
Proof. exact (EQ_MP (@lem511952 _17370 _17371 y x y' P Q h1) (@lem511682 _17370 _17371 y x y' P Q h1)). Qed.
Lemma lem511954 {_17370 _17371 : Type'} (y : _17370) (x : _17371) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term215 _17370 _17371 y x P Q) : False.
Proof. exact (ex_elim (@lem511607 _17370 _17371 y x P Q h1) (fun y' : _17370 => fun h0 : term214 _17370 _17371 y x P Q y' => @lem511953 _17370 _17371 y x y' P Q h0)). Qed.
Lemma lem511955 {_17370 _17371 : Type'} (y : _17370) (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term217 _17370 _17371 y P Q) : False.
Proof. exact (ex_elim (@lem511606 _17370 _17371 y P Q h1) (fun x : _17371 => fun h0 : term216 _17370 _17371 y P Q x => @lem511954 _17370 _17371 y x P Q h0)). Qed.
Lemma lem511956 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term0 _17370 _17371 P Q) : False.
Proof. exact (ex_elim (@lem511605 _17370 _17371 P Q h1) (fun y : _17370 => fun h0 : term218 _17370 _17371 P Q y => @lem511955 _17370 _17371 y P Q h0)). Qed.
Lemma lem511957 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term0 _17370 _17371 P Q) : (term0 _17370 _17371 P Q) = False.
Proof. exact (prop_ext (fun h2 : term0 _17370 _17371 P Q => @lem511956 _17370 _17371 P Q h1) (fun h2 : False => @lem511133 _17370 _17371 P Q h1)). Qed.
Lemma lem511958 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term0 _17370 _17371 P Q) : False.
Proof. exact (EQ_MP (@lem511957 _17370 _17371 P Q h1) (@lem511133 _17370 _17371 P Q h1)). Qed.
Lemma lem511959 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : term1 _17370 _17371 P Q.
Proof. exact (fun h0 : term0 _17370 _17371 P Q => @lem511958 _17370 _17371 P Q h0). Qed.
Lemma lem511960 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term7 _17370 _17371 P Q) = (term8 _17370 _17371 P Q).
Proof. exact (EQ_MP (@lem511132 _17370 _17371 P Q) (@lem511959 _17370 _17371 P Q)). Qed.
Lemma lem511965 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) : term12 _17370 _17371 Q.
Proof. exact (fun P : _17371 -> Prop => @lem511960 _17370 _17371 P Q). Qed.
Lemma lem511970 {_17370 _17371 : Type'} : term16 _17370 _17371.
Proof. exact (fun Q : type1470 _17370 _17371 => @lem511965 _17370 _17371 Q). Qed.
Lemma lem511971 {_17370 _17371 : Type'} : term15 _17370 _17371.
Proof. exact (EQ_MP (@lem511128 _17370 _17371) (@lem511970 _17370 _17371)). Qed.
Lemma lem511972 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) : term251 _17370 _17371 Q.
Proof. exact (@lem511971 _17370 _17371 Q). Qed.
Lemma lem511973 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) : (term251 _17370 _17371 Q) = (term11 _17370 _17371 Q).
Proof. exact (eq_refl (term251 _17370 _17371 Q)). Qed.
Lemma lem511974 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) : term11 _17370 _17371 Q.
Proof. exact (EQ_MP (@lem511973 _17370 _17371 Q) (@lem511972 _17370 _17371 Q)). Qed.
Lemma lem511975 {_17370 _17371 : Type'} (Q : type1470 _17370 _17371) (P : _17371 -> Prop) : term252 _17370 _17371 Q P.
Proof. exact (@lem511974 _17370 _17371 Q P). Qed.
Lemma lem511976 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term252 _17370 _17371 Q P) = (term1 _17370 _17371 P Q).
Proof. exact (eq_refl (term252 _17370 _17371 Q P)). Qed.
Lemma lem511977 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : term1 _17370 _17371 P Q.
Proof. exact (EQ_MP (@lem511976 _17370 _17371 P Q) (@lem511975 _17370 _17371 Q P)). Qed.
Lemma lem511979 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : term1 _17370 _17371 P Q.
Proof. exact (@lem511000 _17370 _17371 P Q (@lem511977 _17370 _17371 P Q)). Qed.
Lemma lem511980 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term0 _17370 _17371 P Q) : False.
Proof. exact (@lem511979 _17370 _17371 P Q (@lem510984 _17370 _17371 P Q h1)). Qed.
Lemma lem511981 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term0 _17370 _17371 P Q) : (term0 _17370 _17371 P Q) = False.
Proof. exact (prop_ext (fun h2 : term0 _17370 _17371 P Q => @lem511980 _17370 _17371 P Q h1) (fun h2 : False => @lem510984 _17370 _17371 P Q h1)). Qed.
Lemma lem511982 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) (h1 : term0 _17370 _17371 P Q) : False.
Proof. exact (EQ_MP (@lem511981 _17370 _17371 P Q h1) (@lem510984 _17370 _17371 P Q h1)). Qed.
Lemma lem511983 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : term1 _17370 _17371 P Q.
Proof. exact (fun h0 : term0 _17370 _17371 P Q => @lem511982 _17370 _17371 P Q h0). Qed.
