Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1097384_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1097121 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem1097122 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem1097123 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem1097122 A B f) (@lem1097121 A B f)). Qed.
Lemma lem1097124 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem1097123 A B f y). Qed.
Lemma lem1097125 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem1097128 {A B : Type'} (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : MAP' = (term4 A B _17946).
Proof. exact (h1). Qed.
Lemma lem1097129 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1097130 {A B : Type'} (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (MAP' f) = (term5 A B _17946 f).
Proof. exact (MK_COMB (@lem1097128 A B MAP' _17946 h1) (@lem1097129 A B f)). Qed.
Lemma lem1097132 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1097125 A B f y) (@lem1097124 A B f y)). Qed.
Lemma lem1097133 {A B : Type'} (f : type540 A B) (y : A -> B) : (term6 A B f y) = (f y).
Proof. exact (@lem1097132 (A -> B) (type1139 A B) f y). Qed.
Lemma lem1097134 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term7 A B _17946 f) = (term5 A B _17946 f).
Proof. exact (@lem1097133 A B (term4 A B _17946) f). Qed.
Lemma lem1097135 {A B : Type'} (_17946 : type1129 A B) (_17944 : A -> B) : (term5 A B _17946 _17944) = (term8 A B _17946 _17944).
Proof. exact (eq_refl (term5 A B _17946 _17944)). Qed.
Lemma lem1097136 {A B : Type'} (_17946 : type1129 A B) : (term9 A B _17946) = (term4 A B _17946).
Proof. exact (fun_ext (fun _17944 : A -> B => @lem1097135 A B _17946 _17944)). Qed.
Lemma lem1097137 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1097138 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term7 A B _17946 f) = (term5 A B _17946 f).
Proof. exact (MK_COMB (@lem1097136 A B _17946) (@lem1097137 A B f)). Qed.
Lemma lem1097139 {A B : Type'} : (@eq ((list A) -> list B)) = (@eq ((list A) -> list B)).
Proof. exact (eq_refl (@eq ((list A) -> list B))). Qed.
Lemma lem1097140 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term10 A B _17946 f) = (term11 A B _17946 f).
Proof. exact (MK_COMB (@lem1097139 A B) (@lem1097138 A B _17946 f)). Qed.
Lemma lem1097141 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term5 A B _17946 f) = (term8 A B _17946 f).
Proof. exact (eq_refl (term5 A B _17946 f)). Qed.
Lemma lem1097142 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : ((term7 A B _17946 f) = (term5 A B _17946 f)) = ((term5 A B _17946 f) = (term8 A B _17946 f)).
Proof. exact (MK_COMB (@lem1097140 A B _17946 f) (@lem1097141 A B _17946 f)). Qed.
Lemma lem1097143 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term5 A B _17946 f) = (term8 A B _17946 f).
Proof. exact (EQ_MP (@lem1097142 A B _17946 f) (@lem1097134 A B _17946 f)). Qed.
Lemma lem1097144 {A B : Type'} (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (MAP' f) = (term8 A B _17946 f).
Proof. exact (TRANS (@lem1097130 A B f MAP' _17946 h1) (@lem1097143 A B _17946 f)). Qed.
Lemma lem1097145 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1097146 {A B : Type'} (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (MAP' f (@nil A)) = (term12 A B _17946 f).
Proof. exact (MK_COMB (@lem1097144 A B f MAP' _17946 h1) (@lem1097145 A)). Qed.
Lemma lem1097148 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1097125 A B f y) (@lem1097124 A B f y)). Qed.
Lemma lem1097149 {A B : Type'} (f : type1139 A B) (y : list A) : (term13 A B f y) = (f y).
Proof. exact (@lem1097148 (list A) (list B) f y). Qed.
Lemma lem1097150 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term14 A B _17946 f) = (term12 A B _17946 f).
Proof. exact (@lem1097149 A B (term8 A B _17946 f) (@nil A)). Qed.
Lemma lem1097151 {A B : Type'} (_17946 : type1129 A B) (_17945 : list A) (f : A -> B) : (term15 A B _17946 f _17945) = (_17946 _17945 f).
Proof. exact (eq_refl (term15 A B _17946 f _17945)). Qed.
Lemma lem1097152 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term16 A B _17946 f) = (term8 A B _17946 f).
Proof. exact (fun_ext (fun _17945 : list A => @lem1097151 A B _17946 _17945 f)). Qed.
Lemma lem1097153 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1097154 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term14 A B _17946 f) = (term12 A B _17946 f).
Proof. exact (MK_COMB (@lem1097152 A B _17946 f) (@lem1097153 A)). Qed.
Lemma lem1097155 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1097156 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term17 A B _17946 f) = (term18 A B _17946 f).
Proof. exact (MK_COMB (@lem1097155 B) (@lem1097154 A B _17946 f)). Qed.
Lemma lem1097157 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term12 A B _17946 f) = (_17946 (@nil A) f).
Proof. exact (eq_refl (term12 A B _17946 f)). Qed.
Lemma lem1097158 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : ((term14 A B _17946 f) = (term12 A B _17946 f)) = ((term12 A B _17946 f) = (_17946 (@nil A) f)).
Proof. exact (MK_COMB (@lem1097156 A B _17946 f) (@lem1097157 A B _17946 f)). Qed.
Lemma lem1097159 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term12 A B _17946 f) = (_17946 (@nil A) f).
Proof. exact (EQ_MP (@lem1097158 A B _17946 f) (@lem1097150 A B _17946 f)). Qed.
Lemma lem1097160 {A B : Type'} (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (MAP' f (@nil A)) = (_17946 (@nil A) f).
Proof. exact (TRANS (@lem1097146 A B f MAP' _17946 h1) (@lem1097159 A B _17946 f)). Qed.
Lemma lem1097161 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1097162 {A B : Type'} (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (term19 A B MAP' f) = (term20 A B _17946 f).
Proof. exact (MK_COMB (@lem1097161 B) (@lem1097160 A B f MAP' _17946 h1)). Qed.
Lemma lem1097163 {B : Type'} : (@nil B) = (@nil B).
Proof. exact (eq_refl (@nil B)). Qed.
Lemma lem1097164 {A B : Type'} (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : ((MAP' f (@nil A)) = (@nil B)) = ((_17946 (@nil A) f) = (@nil B)).
Proof. exact (MK_COMB (@lem1097162 A B f MAP' _17946 h1) (@lem1097163 B)). Qed.
Lemma lem1097165 {A B : Type'} (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (term21 A B MAP') = (term22 A B _17946).
Proof. exact (fun_ext (fun f : A -> B => @lem1097164 A B f MAP' _17946 h1)). Qed.
Lemma lem1097166 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1097167 {A B : Type'} (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (term23 A B MAP') = (term24 A B _17946).
Proof. exact (MK_COMB (@lem1097166 A B) (@lem1097165 A B MAP' _17946 h1)). Qed.
Lemma lem1097168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1097169 {A B : Type'} (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (term25 A B MAP') = (term26 A B _17946).
Proof. exact (MK_COMB (@lem1097168) (@lem1097167 A B MAP' _17946 h1)). Qed.
Lemma lem1097171 {A B : Type'} (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : MAP' = (term4 A B _17946).
Proof. exact (h1). Qed.
Lemma lem1097172 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1097173 {A B : Type'} (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (MAP' f) = (term5 A B _17946 f).
Proof. exact (MK_COMB (@lem1097171 A B MAP' _17946 h1) (@lem1097172 A B f)). Qed.
Lemma lem1097175 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1097125 A B f y) (@lem1097124 A B f y)). Qed.
Lemma lem1097176 {A B : Type'} (f : type540 A B) (y : A -> B) : (term6 A B f y) = (f y).
Proof. exact (@lem1097175 (A -> B) (type1139 A B) f y). Qed.
Lemma lem1097177 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term7 A B _17946 f) = (term5 A B _17946 f).
Proof. exact (@lem1097176 A B (term4 A B _17946) f). Qed.
Lemma lem1097178 {A B : Type'} (_17946 : type1129 A B) (_17944 : A -> B) : (term5 A B _17946 _17944) = (term8 A B _17946 _17944).
Proof. exact (eq_refl (term5 A B _17946 _17944)). Qed.
Lemma lem1097179 {A B : Type'} (_17946 : type1129 A B) : (term9 A B _17946) = (term4 A B _17946).
Proof. exact (fun_ext (fun _17944 : A -> B => @lem1097178 A B _17946 _17944)). Qed.
Lemma lem1097180 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1097181 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term7 A B _17946 f) = (term5 A B _17946 f).
Proof. exact (MK_COMB (@lem1097179 A B _17946) (@lem1097180 A B f)). Qed.
Lemma lem1097182 {A B : Type'} : (@eq ((list A) -> list B)) = (@eq ((list A) -> list B)).
Proof. exact (eq_refl (@eq ((list A) -> list B))). Qed.
Lemma lem1097183 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term10 A B _17946 f) = (term11 A B _17946 f).
Proof. exact (MK_COMB (@lem1097182 A B) (@lem1097181 A B _17946 f)). Qed.
Lemma lem1097184 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term5 A B _17946 f) = (term8 A B _17946 f).
Proof. exact (eq_refl (term5 A B _17946 f)). Qed.
Lemma lem1097185 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : ((term7 A B _17946 f) = (term5 A B _17946 f)) = ((term5 A B _17946 f) = (term8 A B _17946 f)).
Proof. exact (MK_COMB (@lem1097183 A B _17946 f) (@lem1097184 A B _17946 f)). Qed.
Lemma lem1097186 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term5 A B _17946 f) = (term8 A B _17946 f).
Proof. exact (EQ_MP (@lem1097185 A B _17946 f) (@lem1097177 A B _17946 f)). Qed.
Lemma lem1097187 {A B : Type'} (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (MAP' f) = (term8 A B _17946 f).
Proof. exact (TRANS (@lem1097173 A B f MAP' _17946 h1) (@lem1097186 A B _17946 f)). Qed.
Lemma lem1097188 {A : Type'} (h : A) (t : list A) : (@cons A h t) = (@cons A h t).
Proof. exact (eq_refl (@cons A h t)). Qed.
Lemma lem1097189 {A B : Type'} (f : A -> B) (h : A) (t : list A) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (term27 A B MAP' f h t) = (term28 A B _17946 f h t).
Proof. exact (MK_COMB (@lem1097187 A B f MAP' _17946 h1) (@lem1097188 A h t)). Qed.
Lemma lem1097191 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1097125 A B f y) (@lem1097124 A B f y)). Qed.
Lemma lem1097192 {A B : Type'} (f : type1139 A B) (y : list A) : (term13 A B f y) = (f y).
Proof. exact (@lem1097191 (list A) (list B) f y). Qed.
Lemma lem1097193 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) (h : A) (t : list A) : (term29 A B _17946 f h t) = (term28 A B _17946 f h t).
Proof. exact (@lem1097192 A B (term8 A B _17946 f) (@cons A h t)). Qed.
Lemma lem1097194 {A B : Type'} (_17946 : type1129 A B) (_17945 : list A) (f : A -> B) : (term15 A B _17946 f _17945) = (_17946 _17945 f).
Proof. exact (eq_refl (term15 A B _17946 f _17945)). Qed.
Lemma lem1097195 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term16 A B _17946 f) = (term8 A B _17946 f).
Proof. exact (fun_ext (fun _17945 : list A => @lem1097194 A B _17946 _17945 f)). Qed.
Lemma lem1097196 {A : Type'} (h : A) (t : list A) : (@cons A h t) = (@cons A h t).
Proof. exact (eq_refl (@cons A h t)). Qed.
Lemma lem1097197 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) (h : A) (t : list A) : (term29 A B _17946 f h t) = (term28 A B _17946 f h t).
Proof. exact (MK_COMB (@lem1097195 A B _17946 f) (@lem1097196 A h t)). Qed.
Lemma lem1097198 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1097199 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) (h : A) (t : list A) : (term30 A B _17946 f h t) = (term31 A B _17946 f h t).
Proof. exact (MK_COMB (@lem1097198 B) (@lem1097197 A B _17946 f h t)). Qed.
Lemma lem1097200 {A B : Type'} (_17946 : type1129 A B) (h : A) (t : list A) (f : A -> B) : (term28 A B _17946 f h t) = (term32 A B _17946 h t f).
Proof. exact (eq_refl (term28 A B _17946 f h t)). Qed.
Lemma lem1097201 {A B : Type'} (_17946 : type1129 A B) (h : A) (t : list A) (f : A -> B) : ((term29 A B _17946 f h t) = (term28 A B _17946 f h t)) = ((term28 A B _17946 f h t) = (term32 A B _17946 h t f)).
Proof. exact (MK_COMB (@lem1097199 A B _17946 f h t) (@lem1097200 A B _17946 h t f)). Qed.
Lemma lem1097202 {A B : Type'} (_17946 : type1129 A B) (h : A) (t : list A) (f : A -> B) : (term28 A B _17946 f h t) = (term32 A B _17946 h t f).
Proof. exact (EQ_MP (@lem1097201 A B _17946 h t f) (@lem1097193 A B _17946 f h t)). Qed.
Lemma lem1097203 {A B : Type'} (h : A) (t : list A) (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (term27 A B MAP' f h t) = (term32 A B _17946 h t f).
Proof. exact (TRANS (@lem1097189 A B f h t MAP' _17946 h1) (@lem1097202 A B _17946 h t f)). Qed.
Lemma lem1097204 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1097205 {A B : Type'} (h : A) (t : list A) (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (term33 A B MAP' f h t) = (term34 A B _17946 h t f).
Proof. exact (MK_COMB (@lem1097204 B) (@lem1097203 A B h t f MAP' _17946 h1)). Qed.
Lemma lem1097207 {A B : Type'} (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : MAP' = (term4 A B _17946).
Proof. exact (h1). Qed.
Lemma lem1097208 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1097209 {A B : Type'} (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (MAP' f) = (term5 A B _17946 f).
Proof. exact (MK_COMB (@lem1097207 A B MAP' _17946 h1) (@lem1097208 A B f)). Qed.
Lemma lem1097211 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1097125 A B f y) (@lem1097124 A B f y)). Qed.
Lemma lem1097212 {A B : Type'} (f : type540 A B) (y : A -> B) : (term6 A B f y) = (f y).
Proof. exact (@lem1097211 (A -> B) (type1139 A B) f y). Qed.
Lemma lem1097213 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term7 A B _17946 f) = (term5 A B _17946 f).
Proof. exact (@lem1097212 A B (term4 A B _17946) f). Qed.
Lemma lem1097214 {A B : Type'} (_17946 : type1129 A B) (_17944 : A -> B) : (term5 A B _17946 _17944) = (term8 A B _17946 _17944).
Proof. exact (eq_refl (term5 A B _17946 _17944)). Qed.
Lemma lem1097215 {A B : Type'} (_17946 : type1129 A B) : (term9 A B _17946) = (term4 A B _17946).
Proof. exact (fun_ext (fun _17944 : A -> B => @lem1097214 A B _17946 _17944)). Qed.
Lemma lem1097216 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1097217 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term7 A B _17946 f) = (term5 A B _17946 f).
Proof. exact (MK_COMB (@lem1097215 A B _17946) (@lem1097216 A B f)). Qed.
Lemma lem1097218 {A B : Type'} : (@eq ((list A) -> list B)) = (@eq ((list A) -> list B)).
Proof. exact (eq_refl (@eq ((list A) -> list B))). Qed.
Lemma lem1097219 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term10 A B _17946 f) = (term11 A B _17946 f).
Proof. exact (MK_COMB (@lem1097218 A B) (@lem1097217 A B _17946 f)). Qed.
Lemma lem1097220 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term5 A B _17946 f) = (term8 A B _17946 f).
Proof. exact (eq_refl (term5 A B _17946 f)). Qed.
Lemma lem1097221 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : ((term7 A B _17946 f) = (term5 A B _17946 f)) = ((term5 A B _17946 f) = (term8 A B _17946 f)).
Proof. exact (MK_COMB (@lem1097219 A B _17946 f) (@lem1097220 A B _17946 f)). Qed.
Lemma lem1097222 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term5 A B _17946 f) = (term8 A B _17946 f).
Proof. exact (EQ_MP (@lem1097221 A B _17946 f) (@lem1097213 A B _17946 f)). Qed.
Lemma lem1097223 {A B : Type'} (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (MAP' f) = (term8 A B _17946 f).
Proof. exact (TRANS (@lem1097209 A B f MAP' _17946 h1) (@lem1097222 A B _17946 f)). Qed.
Lemma lem1097224 {A : Type'} (t : list A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1097225 {A B : Type'} (f : A -> B) (t : list A) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (MAP' f t) = (term15 A B _17946 f t).
Proof. exact (MK_COMB (@lem1097223 A B f MAP' _17946 h1) (@lem1097224 A t)). Qed.
Lemma lem1097227 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1097125 A B f y) (@lem1097124 A B f y)). Qed.
Lemma lem1097228 {A B : Type'} (f : type1139 A B) (y : list A) : (term13 A B f y) = (f y).
Proof. exact (@lem1097227 (list A) (list B) f y). Qed.
Lemma lem1097229 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) (t : list A) : (term35 A B _17946 f t) = (term15 A B _17946 f t).
Proof. exact (@lem1097228 A B (term8 A B _17946 f) t). Qed.
Lemma lem1097230 {A B : Type'} (_17946 : type1129 A B) (_17945 : list A) (f : A -> B) : (term15 A B _17946 f _17945) = (_17946 _17945 f).
Proof. exact (eq_refl (term15 A B _17946 f _17945)). Qed.
Lemma lem1097231 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term16 A B _17946 f) = (term8 A B _17946 f).
Proof. exact (fun_ext (fun _17945 : list A => @lem1097230 A B _17946 _17945 f)). Qed.
Lemma lem1097232 {A : Type'} (t : list A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1097233 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) (t : list A) : (term35 A B _17946 f t) = (term15 A B _17946 f t).
Proof. exact (MK_COMB (@lem1097231 A B _17946 f) (@lem1097232 A t)). Qed.
Lemma lem1097234 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1097235 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) (t : list A) : (term36 A B _17946 f t) = (term37 A B _17946 f t).
Proof. exact (MK_COMB (@lem1097234 B) (@lem1097233 A B _17946 f t)). Qed.
Lemma lem1097236 {A B : Type'} (_17946 : type1129 A B) (t : list A) (f : A -> B) : (term15 A B _17946 f t) = (_17946 t f).
Proof. exact (eq_refl (term15 A B _17946 f t)). Qed.
Lemma lem1097237 {A B : Type'} (_17946 : type1129 A B) (t : list A) (f : A -> B) : ((term35 A B _17946 f t) = (term15 A B _17946 f t)) = ((term15 A B _17946 f t) = (_17946 t f)).
Proof. exact (MK_COMB (@lem1097235 A B _17946 f t) (@lem1097236 A B _17946 t f)). Qed.
Lemma lem1097238 {A B : Type'} (_17946 : type1129 A B) (t : list A) (f : A -> B) : (term15 A B _17946 f t) = (_17946 t f).
Proof. exact (EQ_MP (@lem1097237 A B _17946 t f) (@lem1097229 A B _17946 f t)). Qed.
Lemma lem1097239 {A B : Type'} (t : list A) (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (MAP' f t) = (_17946 t f).
Proof. exact (TRANS (@lem1097225 A B f t MAP' _17946 h1) (@lem1097238 A B _17946 t f)). Qed.
Lemma lem1097240 {A B : Type'} (f : A -> B) (h : A) : (term38 A B f h) = (term38 A B f h).
Proof. exact (eq_refl (term38 A B f h)). Qed.
Lemma lem1097241 {A B : Type'} (h : A) (t : list A) (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (term39 A B h MAP' f t) = (term40 A B h _17946 t f).
Proof. exact (MK_COMB (@lem1097240 A B f h) (@lem1097239 A B t f MAP' _17946 h1)). Qed.
Lemma lem1097242 {A B : Type'} (h : A) (t : list A) (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : ((term27 A B MAP' f h t) = (term39 A B h MAP' f t)) = ((term32 A B _17946 h t f) = (term40 A B h _17946 t f)).
Proof. exact (MK_COMB (@lem1097205 A B h t f MAP' _17946 h1) (@lem1097241 A B h t f MAP' _17946 h1)). Qed.
Lemma lem1097243 {A B : Type'} (h : A) (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (term41 A B h MAP' f) = (term42 A B h _17946 f).
Proof. exact (fun_ext (fun t : list A => @lem1097242 A B h t f MAP' _17946 h1)). Qed.
Lemma lem1097244 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1097245 {A B : Type'} (h : A) (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (term43 A B h MAP' f) = (term44 A B h _17946 f).
Proof. exact (MK_COMB (@lem1097244 A) (@lem1097243 A B h f MAP' _17946 h1)). Qed.
Lemma lem1097246 {A B : Type'} (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (term45 A B MAP' f) = (term46 A B _17946 f).
Proof. exact (fun_ext (fun h : A => @lem1097245 A B h f MAP' _17946 h1)). Qed.
Lemma lem1097247 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1097248 {A B : Type'} (f : A -> B) (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (term47 A B MAP' f) = (term48 A B _17946 f).
Proof. exact (MK_COMB (@lem1097247 A) (@lem1097246 A B f MAP' _17946 h1)). Qed.
Lemma lem1097249 {A B : Type'} (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (term49 A B MAP') = (term50 A B _17946).
Proof. exact (fun_ext (fun f : A -> B => @lem1097248 A B f MAP' _17946 h1)). Qed.
Lemma lem1097250 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1097251 {A B : Type'} (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (term51 A B MAP') = (term52 A B _17946).
Proof. exact (MK_COMB (@lem1097250 A B) (@lem1097249 A B MAP' _17946 h1)). Qed.
Lemma lem1097252 {A B : Type'} (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (term53 A B MAP') = (term54 A B _17946).
Proof. exact (MK_COMB (@lem1097169 A B MAP' _17946 h1) (@lem1097251 A B MAP' _17946 h1)). Qed.
Lemma lem1097253 {A B : Type'} (_17946 : type1129 A B) (h1 : (_17946 (@nil A)) = (term55 A B)) : (_17946 (@nil A)) = (term55 A B).
Proof. exact (h1). Qed.
Lemma lem1097254 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1097255 {A B : Type'} (f : A -> B) (_17946 : type1129 A B) (h1 : (_17946 (@nil A)) = (term55 A B)) : (_17946 (@nil A) f) = (term56 A B f).
Proof. exact (MK_COMB (@lem1097253 A B _17946 h1) (@lem1097254 A B f)). Qed.
Lemma lem1097256 {A B : Type'} (f : A -> B) : (term56 A B f) = (@nil B).
Proof. exact (eq_refl (term56 A B f)). Qed.
Lemma lem1097257 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : (term20 A B _17946 f) = (term20 A B _17946 f).
Proof. exact (eq_refl (term20 A B _17946 f)). Qed.
Lemma lem1097258 {A B : Type'} (_17946 : type1129 A B) (f : A -> B) : ((_17946 (@nil A) f) = (term56 A B f)) = ((_17946 (@nil A) f) = (@nil B)).
Proof. exact (MK_COMB (@lem1097257 A B _17946 f) (@lem1097256 A B f)). Qed.
Lemma lem1097259 {A B : Type'} (f : A -> B) (_17946 : type1129 A B) (h1 : (_17946 (@nil A)) = (term55 A B)) : (_17946 (@nil A) f) = (@nil B).
Proof. exact (EQ_MP (@lem1097258 A B _17946 f) (@lem1097255 A B f _17946 h1)). Qed.
Lemma lem1097260 {A B : Type'} (_17946 : type1129 A B) (h1 : (_17946 (@nil A)) = (term55 A B)) : term24 A B _17946.
Proof. exact (fun f : A -> B => @lem1097259 A B f _17946 h1). Qed.
Lemma lem1097261 {A B : Type'} (_17946 : type1129 A B) (h1 : term57 A B _17946) : term57 A B _17946.
Proof. exact (h1). Qed.
Lemma lem1097262 {A B : Type'} (h : A) (_17946 : type1129 A B) (h1 : term57 A B _17946) : term58 A B _17946 h.
Proof. exact (@lem1097261 A B _17946 h1 h). Qed.
Lemma lem1097263 {A B : Type'} (h : A) (_17946 : type1129 A B) : (term58 A B _17946 h) = (term59 A B h _17946).
Proof. exact (eq_refl (term58 A B _17946 h)). Qed.
Lemma lem1097264 {A B : Type'} (h : A) (_17946 : type1129 A B) (h1 : term57 A B _17946) : term59 A B h _17946.
Proof. exact (EQ_MP (@lem1097263 A B h _17946) (@lem1097262 A B h _17946 h1)). Qed.
Lemma lem1097265 {A B : Type'} (h : A) (t : list A) (_17946 : type1129 A B) (h1 : term57 A B _17946) : term60 A B h _17946 t.
Proof. exact (@lem1097264 A B h _17946 h1 t). Qed.
Lemma lem1097266 {A B : Type'} (h : A) (_17946 : type1129 A B) (t : list A) : (term60 A B h _17946 t) = ((term61 A B _17946 h t) = (term62 A B h _17946 t)).
Proof. exact (eq_refl (term60 A B h _17946 t)). Qed.
Lemma lem1097267 {A B : Type'} (h : A) (t : list A) (_17946 : type1129 A B) (h1 : term57 A B _17946) : (term61 A B _17946 h t) = (term62 A B h _17946 t).
Proof. exact (EQ_MP (@lem1097266 A B h _17946 t) (@lem1097265 A B h t _17946 h1)). Qed.
Lemma lem1097268 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1097269 {A B : Type'} (h : A) (t : list A) (f : A -> B) (_17946 : type1129 A B) (h1 : term57 A B _17946) : (term32 A B _17946 h t f) = (term63 A B h _17946 t f).
Proof. exact (MK_COMB (@lem1097267 A B h t _17946 h1) (@lem1097268 A B f)). Qed.
Lemma lem1097270 {A B : Type'} (h : A) (_17946 : type1129 A B) (t : list A) (f : A -> B) : (term63 A B h _17946 t f) = (term40 A B h _17946 t f).
Proof. exact (eq_refl (term63 A B h _17946 t f)). Qed.
Lemma lem1097271 {A B : Type'} (_17946 : type1129 A B) (h : A) (t : list A) (f : A -> B) : (term34 A B _17946 h t f) = (term34 A B _17946 h t f).
Proof. exact (eq_refl (term34 A B _17946 h t f)). Qed.
Lemma lem1097272 {A B : Type'} (h : A) (_17946 : type1129 A B) (t : list A) (f : A -> B) : ((term32 A B _17946 h t f) = (term63 A B h _17946 t f)) = ((term32 A B _17946 h t f) = (term40 A B h _17946 t f)).
Proof. exact (MK_COMB (@lem1097271 A B _17946 h t f) (@lem1097270 A B h _17946 t f)). Qed.
Lemma lem1097273 {A B : Type'} (h : A) (t : list A) (f : A -> B) (_17946 : type1129 A B) (h1 : term57 A B _17946) : (term32 A B _17946 h t f) = (term40 A B h _17946 t f).
Proof. exact (EQ_MP (@lem1097272 A B h _17946 t f) (@lem1097269 A B h t f _17946 h1)). Qed.
Lemma lem1097274 {A B : Type'} (h : A) (f : A -> B) (_17946 : type1129 A B) (h1 : term57 A B _17946) : term44 A B h _17946 f.
Proof. exact (fun t : list A => @lem1097273 A B h t f _17946 h1). Qed.
Lemma lem1097275 {A B : Type'} (f : A -> B) (_17946 : type1129 A B) (h1 : term57 A B _17946) : term48 A B _17946 f.
Proof. exact (fun h : A => @lem1097274 A B h f _17946 h1). Qed.
Lemma lem1097276 {A B : Type'} (_17946 : type1129 A B) (h1 : term57 A B _17946) : term52 A B _17946.
Proof. exact (fun f : A -> B => @lem1097275 A B f _17946 h1). Qed.
Lemma lem1097277 {A B : Type'} (_17946 : type1129 A B) (h1 : term64 A B _17946) : term64 A B _17946.
Proof. exact (h1). Qed.
Lemma lem1097278 {A B : Type'} (_17946 : type1129 A B) (h1 : term64 A B _17946) : term57 A B _17946.
Proof. exact (proj2 (@lem1097277 A B _17946 h1)). Qed.
Lemma lem1097279 {A B : Type'} (_17946 : type1129 A B) (h1 : term64 A B _17946) : (_17946 (@nil A)) = (term55 A B).
Proof. exact (proj1 (@lem1097277 A B _17946 h1)). Qed.
Lemma lem1097280 {A B : Type'} (_17946 : type1129 A B) (h1 : term64 A B _17946) : ((_17946 (@nil A)) = (term55 A B)) = (term24 A B _17946).
Proof. exact (prop_ext (fun h2 : (_17946 (@nil A)) = (term55 A B) => @lem1097260 A B _17946 h2) (fun h2 : term24 A B _17946 => @lem1097279 A B _17946 h1)). Qed.
Lemma lem1097281 {A B : Type'} (_17946 : type1129 A B) (h1 : term64 A B _17946) : term24 A B _17946.
Proof. exact (EQ_MP (@lem1097280 A B _17946 h1) (@lem1097279 A B _17946 h1)). Qed.
Lemma lem1097282 {A B : Type'} (_17946 : type1129 A B) (h1 : term64 A B _17946) : (term57 A B _17946) = (term52 A B _17946).
Proof. exact (prop_ext (fun h2 : term57 A B _17946 => @lem1097276 A B _17946 h2) (fun h2 : term52 A B _17946 => @lem1097278 A B _17946 h1)). Qed.
Lemma lem1097283 {A B : Type'} (_17946 : type1129 A B) (h1 : term64 A B _17946) : term52 A B _17946.
Proof. exact (EQ_MP (@lem1097282 A B _17946 h1) (@lem1097278 A B _17946 h1)). Qed.
Lemma lem1097284 {A B : Type'} (_17946 : type1129 A B) (h1 : term64 A B _17946) : term54 A B _17946.
Proof. exact (conj (@lem1097281 A B _17946 h1) (@lem1097283 A B _17946 h1)). Qed.
Lemma lem1097285 {A Z : Type'} (NIL' : Z) : term65 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1097286 {A Z : Type'} (NIL' : Z) : (term65 A Z NIL') = (term66 A Z NIL').
Proof. exact (eq_refl (term65 A Z NIL')). Qed.
Lemma lem1097287 {A Z : Type'} (NIL' : Z) : term66 A Z NIL'.
Proof. exact (EQ_MP (@lem1097286 A Z NIL') (@lem1097285 A Z NIL')). Qed.
Lemma lem1097288 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term67 A Z NIL' CONS'.
Proof. exact (@lem1097287 A Z NIL' CONS'). Qed.
Lemma lem1097289 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term67 A Z NIL' CONS') = (term68 A Z NIL' CONS').
Proof. exact (eq_refl (term67 A Z NIL' CONS')). Qed.
Lemma lem1097290 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term68 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1097289 A Z NIL' CONS') (@lem1097288 A Z NIL' CONS')). Qed.
Lemma lem1097291 {A B : Type'} (NIL' : type568 A B) (CONS' : type1385 A B) : term69 A B NIL' CONS'.
Proof. exact (@lem1097290 A (type568 A B) NIL' CONS'). Qed.
Lemma lem1097292 {A B : Type'} : term70 A B.
Proof. exact (@lem1097291 A B (term55 A B) (term71 A B)). Qed.
Lemma lem1097293 {A B : Type'} (a0 : A) : (term72 A B a0) = (term73 A B a0).
Proof. exact (eq_refl (term72 A B a0)). Qed.
Lemma lem1097294 {A : Type'} (a1 : list A) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1097295 {A B : Type'} (a0 : A) (a1 : list A) : (term74 A B a0 a1) = (term75 A B a0 a1).
Proof. exact (MK_COMB (@lem1097293 A B a0) (@lem1097294 A a1)). Qed.
Lemma lem1097296 {A B : Type'} (a1 : list A) (a0 : A) : (term75 A B a0 a1) = (term76 A B a0).
Proof. exact (eq_refl (term75 A B a0 a1)). Qed.
Lemma lem1097297 {A B : Type'} (a1 : list A) (a0 : A) : (term74 A B a0 a1) = (term76 A B a0).
Proof. exact (TRANS (@lem1097295 A B a0 a1) (@lem1097296 A B a1 a0)). Qed.
Lemma lem1097298 {A B : Type'} (fn : type1129 A B) (a1 : list A) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1097299 {A B : Type'} (a0 : A) (fn : type1129 A B) (a1 : list A) : (term77 A B a0 fn a1) = (term78 A B a0 fn a1).
Proof. exact (MK_COMB (@lem1097297 A B a1 a0) (@lem1097298 A B fn a1)). Qed.
Lemma lem1097300 {A B : Type'} (a0 : A) (fn : type1129 A B) (a1 : list A) : (term78 A B a0 fn a1) = (term62 A B a0 fn a1).
Proof. exact (eq_refl (term78 A B a0 fn a1)). Qed.
Lemma lem1097301 {A B : Type'} (a0 : A) (fn : type1129 A B) (a1 : list A) : (term77 A B a0 fn a1) = (term62 A B a0 fn a1).
Proof. exact (TRANS (@lem1097299 A B a0 fn a1) (@lem1097300 A B a0 fn a1)). Qed.
Lemma lem1097302 {A B : Type'} (fn : type1129 A B) (a0 : A) (a1 : list A) : (term79 A B fn a0 a1) = (term79 A B fn a0 a1).
Proof. exact (eq_refl (term79 A B fn a0 a1)). Qed.
Lemma lem1097303 {A B : Type'} (a0 : A) (fn : type1129 A B) (a1 : list A) : ((term61 A B fn a0 a1) = (term77 A B a0 fn a1)) = ((term61 A B fn a0 a1) = (term62 A B a0 fn a1)).
Proof. exact (MK_COMB (@lem1097302 A B fn a0 a1) (@lem1097301 A B a0 fn a1)). Qed.
Lemma lem1097304 {A B : Type'} (a0 : A) (fn : type1129 A B) : (term80 A B a0 fn) = (term81 A B a0 fn).
Proof. exact (fun_ext (fun a1 : list A => @lem1097303 A B a0 fn a1)). Qed.
Lemma lem1097305 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1097306 {A B : Type'} (a0 : A) (fn : type1129 A B) : (term82 A B a0 fn) = (term59 A B a0 fn).
Proof. exact (MK_COMB (@lem1097305 A) (@lem1097304 A B a0 fn)). Qed.
Lemma lem1097307 {A B : Type'} (fn : type1129 A B) : (term83 A B fn) = (term84 A B fn).
Proof. exact (fun_ext (fun a0 : A => @lem1097306 A B a0 fn)). Qed.
Lemma lem1097308 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1097309 {A B : Type'} (fn : type1129 A B) : (term85 A B fn) = (term57 A B fn).
Proof. exact (MK_COMB (@lem1097308 A) (@lem1097307 A B fn)). Qed.
Lemma lem1097310 {A B : Type'} (fn : type1129 A B) : (term86 A B fn) = (term86 A B fn).
Proof. exact (eq_refl (term86 A B fn)). Qed.
Lemma lem1097311 {A B : Type'} (fn : type1129 A B) : (term87 A B fn) = (term64 A B fn).
Proof. exact (MK_COMB (@lem1097310 A B fn) (@lem1097309 A B fn)). Qed.
Lemma lem1097312 {A B : Type'} : (term88 A B) = (term89 A B).
Proof. exact (fun_ext (fun fn : type1129 A B => @lem1097311 A B fn)). Qed.
Lemma lem1097313 {A B : Type'} : (@ex ((list A) -> (A -> B) -> list B)) = (@ex ((list A) -> (A -> B) -> list B)).
Proof. exact (eq_refl (@ex ((list A) -> (A -> B) -> list B))). Qed.
Lemma lem1097314 {A B : Type'} : (term70 A B) = (term90 A B).
Proof. exact (MK_COMB (@lem1097313 A B) (@lem1097312 A B)). Qed.
Lemma lem1097315 {A B : Type'} : term90 A B.
Proof. exact (EQ_MP (@lem1097314 A B) (@lem1097292 A B)). Qed.
Lemma lem1097316 {A B : Type'} (_17946 : type1129 A B) (h1 : term64 A B _17946) : term64 A B _17946.
Proof. exact (h1). Qed.
Lemma lem1097317 {A B : Type'} (_17946 : type1129 A B) (h1 : term64 A B _17946) : term57 A B _17946.
Proof. exact (proj2 (@lem1097316 A B _17946 h1)). Qed.
Lemma lem1097318 {A B : Type'} (_17946 : type1129 A B) (h1 : term64 A B _17946) : (_17946 (@nil A)) = (term55 A B).
Proof. exact (proj1 (@lem1097316 A B _17946 h1)). Qed.
Lemma lem1097319 {A B : Type'} (_17946 : type1129 A B) (h1 : term64 A B _17946) : term64 A B _17946.
Proof. exact (conj (@lem1097318 A B _17946 h1) (@lem1097317 A B _17946 h1)). Qed.
Lemma lem1097320 {A B : Type'} (_17946 : type1129 A B) (h1 : term64 A B _17946) : term90 A B.
Proof. exact (ex_intro (term89 A B) _17946 (@lem1097319 A B _17946 h1)). Qed.
Lemma lem1097321 {A B : Type'} (h1 : term90 A B) : term90 A B.
Proof. exact (h1). Qed.
Lemma lem1097322 {A B : Type'} (h1 : term90 A B) : term90 A B.
Proof. exact (ex_elim (@lem1097321 A B h1) (fun _17946 : type1129 A B => fun h0 : term89 A B _17946 => @lem1097320 A B _17946 h0)). Qed.
Lemma lem1097323 {A B : Type'} : (term90 A B) = (term90 A B).
Proof. exact (prop_ext (fun h1 : term90 A B => @lem1097322 A B h1) (fun h1 : term90 A B => @lem1097315 A B)). Qed.
Lemma lem1097324 {A B : Type'} : term90 A B.
Proof. exact (EQ_MP (@lem1097323 A B) (@lem1097315 A B)). Qed.
Lemma lem1097325 {A B : Type'} (_17946 : type1129 A B) (h1 : term64 A B _17946) : term91 A B.
Proof. exact (ex_intro (term92 A B) _17946 (@lem1097284 A B _17946 h1)). Qed.
Lemma lem1097326 {A B : Type'} (h1 : term90 A B) : term90 A B.
Proof. exact (h1). Qed.
Lemma lem1097327 {A B : Type'} (h1 : term90 A B) : term91 A B.
Proof. exact (ex_elim (@lem1097326 A B h1) (fun _17946 : type1129 A B => fun h0 : term89 A B _17946 => @lem1097325 A B _17946 h0)). Qed.
Lemma lem1097328 {A B : Type'} : (term90 A B) = (term91 A B).
Proof. exact (prop_ext (fun h1 : term90 A B => @lem1097327 A B h1) (fun h1 : term91 A B => @lem1097324 A B)). Qed.
Lemma lem1097329 {A B : Type'} : term91 A B.
Proof. exact (EQ_MP (@lem1097328 A B) (@lem1097324 A B)). Qed.
Lemma lem1097330 {A B : Type'} (_17946 : type1129 A B) (h1 : term54 A B _17946) : term54 A B _17946.
Proof. exact (h1). Qed.
Lemma lem1097331 {A B : Type'} (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : MAP' = (term4 A B _17946)) : (term54 A B _17946) = (term53 A B MAP').
Proof. exact (SYM (@lem1097252 A B MAP' _17946 h1)). Qed.
Lemma lem1097332 {A B : Type'} (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : term54 A B _17946) (h2 : MAP' = (term4 A B _17946)) : term53 A B MAP'.
Proof. exact (EQ_MP (@lem1097331 A B MAP' _17946 h2) (@lem1097330 A B _17946 h1)). Qed.
Lemma lem1097333 {A B : Type'} (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : term54 A B _17946) (h2 : MAP' = (term4 A B _17946)) : term93 A B.
Proof. exact (ex_intro (term94 A B) MAP' (@lem1097332 A B MAP' _17946 h1 h2)). Qed.
Lemma lem1097334 {A B : Type'} (_17946 : type1129 A B) : (term4 A B _17946) = (term4 A B _17946).
Proof. exact (eq_refl (term4 A B _17946)). Qed.
Lemma lem1097335 {A B : Type'} (MAP' : type540 A B) (_17946 : type1129 A B) (h1 : term54 A B _17946) : term95 A B MAP' _17946.
Proof. exact (fun h0 : MAP' = (term4 A B _17946) => @lem1097333 A B MAP' _17946 h1 h0). Qed.
Lemma lem1097336 {A B : Type'} (_17946 : type1129 A B) (h1 : term54 A B _17946) : term96 A B _17946.
Proof. exact (@lem1097335 A B (term4 A B _17946) _17946 h1). Qed.
Lemma lem1097337 {A B : Type'} (_17946 : type1129 A B) (h1 : term54 A B _17946) : term93 A B.
Proof. exact (@lem1097336 A B _17946 h1 (@lem1097334 A B _17946)). Qed.
Lemma lem1097338 {A B : Type'} (h1 : term91 A B) : term91 A B.
Proof. exact (h1). Qed.
Lemma lem1097339 {A B : Type'} (h1 : term91 A B) : term93 A B.
Proof. exact (ex_elim (@lem1097338 A B h1) (fun _17946 : type1129 A B => fun h0 : term92 A B _17946 => @lem1097337 A B _17946 h0)). Qed.
Lemma lem1097340 {A B : Type'} : (term91 A B) = (term93 A B).
Proof. exact (prop_ext (fun h1 : term91 A B => @lem1097339 A B h1) (fun h1 : term93 A B => @lem1097329 A B)). Qed.
Lemma lem1097341 {A B : Type'} : term93 A B.
Proof. exact (EQ_MP (@lem1097340 A B) (@lem1097329 A B)). Qed.
Lemma lem1097342 {A B : Type'} : term97 A B.
Proof. exact (fun _17950 : type1674 => @lem1097341 A B). Qed.
Lemma lem1097343 {A B : Type'} (P : type1413 A B) : term98 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1097344 {A B : Type'} (P : type1413 A B) : (term98 A B P) = ((term99 A B P) = (term100 A B P)).
Proof. exact (eq_refl (term98 A B P)). Qed.
Lemma lem1097347 {A B : Type'} (P : type1413 A B) : (term99 A B P) = (term100 A B P).
Proof. exact (EQ_MP (@lem1097344 A B P) (@lem1097343 A B P)). Qed.
Lemma lem1097348 {A B : Type'} (P : type1293 A B) : (term101 A B P) = (term102 A B P).
Proof. exact (@lem1097347 type1674 (type540 A B) P). Qed.
Lemma lem1097349 {A B : Type'} : (term103 A B) = (term104 A B).
Proof. exact (@lem1097348 A B (term105 A B)). Qed.
Lemma lem1097350 {A B : Type'} (_17950 : type1674) : (term106 A B _17950) = (term94 A B).
Proof. exact (eq_refl (term106 A B _17950)). Qed.
Lemma lem1097351 {A B : Type'} (MAP' : type540 A B) : MAP' = MAP'.
Proof. exact (eq_refl MAP'). Qed.
Lemma lem1097352 {A B : Type'} (_17950 : type1674) (MAP' : type540 A B) : (term107 A B _17950 MAP') = (term108 A B MAP').
Proof. exact (MK_COMB (@lem1097350 A B _17950) (@lem1097351 A B MAP')). Qed.
Lemma lem1097353 {A B : Type'} (MAP' : type540 A B) : (term108 A B MAP') = (term53 A B MAP').
Proof. exact (eq_refl (term108 A B MAP')). Qed.
Lemma lem1097354 {A B : Type'} (_17950 : type1674) (MAP' : type540 A B) : (term107 A B _17950 MAP') = (term53 A B MAP').
Proof. exact (TRANS (@lem1097352 A B _17950 MAP') (@lem1097353 A B MAP')). Qed.
Lemma lem1097355 {A B : Type'} (_17950 : type1674) : (term109 A B _17950) = (term94 A B).
Proof. exact (fun_ext (fun MAP' : type540 A B => @lem1097354 A B _17950 MAP')). Qed.
Lemma lem1097356 {A B : Type'} : (@ex ((A -> B) -> (list A) -> list B)) = (@ex ((A -> B) -> (list A) -> list B)).
Proof. exact (eq_refl (@ex ((A -> B) -> (list A) -> list B))). Qed.
Lemma lem1097357 {A B : Type'} (_17950 : type1674) : (term110 A B _17950) = (term93 A B).
Proof. exact (MK_COMB (@lem1097356 A B) (@lem1097355 A B _17950)). Qed.
Lemma lem1097358 {A B : Type'} : (term111 A B) = (term112 A B).
Proof. exact (fun_ext (fun _17950 : type1674 => @lem1097357 A B _17950)). Qed.
Lemma lem1097359 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem1097360 {A B : Type'} : (term103 A B) = (term97 A B).
Proof. exact (MK_COMB (@lem1097359) (@lem1097358 A B)). Qed.
Lemma lem1097361 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1097362 {A B : Type'} : (term113 A B) = (term114 A B).
Proof. exact (MK_COMB (@lem1097361) (@lem1097360 A B)). Qed.
Lemma lem1097363 {A B : Type'} (_17950 : type1674) : (term106 A B _17950) = (term94 A B).
Proof. exact (eq_refl (term106 A B _17950)). Qed.
Lemma lem1097364 {A B : Type'} (MAP' : type1297 A B) (_17950 : type1674) : (MAP' _17950) = (MAP' _17950).
Proof. exact (eq_refl (MAP' _17950)). Qed.
Lemma lem1097365 {A B : Type'} (MAP' : type1297 A B) (_17950 : type1674) : (term115 A B MAP' _17950) = (term116 A B MAP' _17950).
Proof. exact (MK_COMB (@lem1097363 A B _17950) (@lem1097364 A B MAP' _17950)). Qed.
Lemma lem1097366 {A B : Type'} (MAP' : type1297 A B) (_17950 : type1674) : (term116 A B MAP' _17950) = (term117 A B MAP' _17950).
Proof. exact (eq_refl (term116 A B MAP' _17950)). Qed.
Lemma lem1097367 {A B : Type'} (MAP' : type1297 A B) (_17950 : type1674) : (term115 A B MAP' _17950) = (term117 A B MAP' _17950).
Proof. exact (TRANS (@lem1097365 A B MAP' _17950) (@lem1097366 A B MAP' _17950)). Qed.
Lemma lem1097368 {A B : Type'} (MAP' : type1297 A B) : (term118 A B MAP') = (term119 A B MAP').
Proof. exact (fun_ext (fun _17950 : type1674 => @lem1097367 A B MAP' _17950)). Qed.
Lemma lem1097369 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem1097370 {A B : Type'} (MAP' : type1297 A B) : (term120 A B MAP') = (term121 A B MAP').
Proof. exact (MK_COMB (@lem1097369) (@lem1097368 A B MAP')). Qed.
Lemma lem1097371 {A B : Type'} : (term122 A B) = (term123 A B).
Proof. exact (fun_ext (fun MAP' : type1297 A B => @lem1097370 A B MAP')). Qed.
Lemma lem1097372 {A B : Type'} : (@ex ((prod nat (prod nat nat)) -> (A -> B) -> (list A) -> list B)) = (@ex ((prod nat (prod nat nat)) -> (A -> B) -> (list A) -> list B)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat nat)) -> (A -> B) -> (list A) -> list B))). Qed.
Lemma lem1097373 {A B : Type'} : (term104 A B) = (term124 A B).
Proof. exact (MK_COMB (@lem1097372 A B) (@lem1097371 A B)). Qed.
Lemma lem1097374 {A B : Type'} : ((term103 A B) = (term104 A B)) = ((term97 A B) = (term124 A B)).
Proof. exact (MK_COMB (@lem1097362 A B) (@lem1097373 A B)). Qed.
Lemma lem1097375 {A B : Type'} : (term97 A B) = (term124 A B).
Proof. exact (EQ_MP (@lem1097374 A B) (@lem1097349 A B)). Qed.
Lemma lem1097376 {A B : Type'} : term124 A B.
Proof. exact (EQ_MP (@lem1097375 A B) (@lem1097342 A B)). Qed.
Lemma lem1097378 {A : Type'} : (@ex A) = (term125 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1097379 {A B : Type'} : (@ex ((prod nat (prod nat nat)) -> (A -> B) -> (list A) -> list B)) = (term126 A B).
Proof. exact (@lem1097378 (type1297 A B)). Qed.
Lemma lem1097380 {A B : Type'} : (term123 A B) = (term123 A B).
Proof. exact (eq_refl (term123 A B)). Qed.
Lemma lem1097381 {A B : Type'} : (term124 A B) = (term127 A B).
Proof. exact (MK_COMB (@lem1097379 A B) (@lem1097380 A B)). Qed.
Lemma lem1097382 {A B : Type'} : (term127 A B) = (term128 A B).
Proof. exact (eq_refl (term127 A B)). Qed.
Lemma lem1097383 {A B : Type'} : (term124 A B) = (term128 A B).
Proof. exact (TRANS (@lem1097381 A B) (@lem1097382 A B)). Qed.
Lemma lem1097384 {A B : Type'} : term128 A B.
Proof. exact (EQ_MP (@lem1097383 A B) (@lem1097376 A B)). Qed.
