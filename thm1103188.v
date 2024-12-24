Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1103188_term_abbrevs.
Require Import thm1102759_spec.
Require Import thm1103131_spec.
Lemma lem1103132 {_25376 : Type'} : (term0 _25376) = (term1 _25376).
Proof. exact (eq_refl (term0 _25376)). Qed.
Lemma lem1103133 {_25376 : Type'} : term1 _25376.
Proof. exact (EQ_MP (@lem1103132 _25376) (@lem1102759 _25376)). Qed.
Lemma lem1103134 {_25376 : Type'} : term2 _25376.
Proof. exact (@lem1103133 _25376 term3). Qed.
Lemma lem1103135 {_25376 : Type'} : (term2 _25376) = (term4 _25376).
Proof. exact (eq_refl (term2 _25376)). Qed.
Lemma lem1103136 {_25376 : Type'} : term4 _25376.
Proof. exact (EQ_MP (@lem1103135 _25376) (@lem1103134 _25376)). Qed.
Lemma lem1103137 {_25376 : Type'} (h1 : (@List.In _25376) = (term5 _25376)) : (@List.In _25376) = (term5 _25376).
Proof. exact (h1). Qed.
Lemma lem1103138 {_25376 : Type'} (h1 : (@List.In _25376) = (term5 _25376)) : (term5 _25376) = (@List.In _25376).
Proof. exact (SYM (@lem1103137 _25376 h1)). Qed.
Lemma lem1103139 {_25376 : Type'} (h1 : (term5 _25376) = (@List.In _25376)) : (term5 _25376) = (@List.In _25376).
Proof. exact (h1). Qed.
Lemma lem1103140 {_25376 : Type'} (h1 : (term5 _25376) = (@List.In _25376)) : (@List.In _25376) = (term5 _25376).
Proof. exact (SYM (@lem1103139 _25376 h1)). Qed.
Lemma lem1103141 {_25376 : Type'} : ((@List.In _25376) = (term5 _25376)) = ((term5 _25376) = (@List.In _25376)).
Proof. exact (prop_ext (fun h1 : (@List.In _25376) = (term5 _25376) => @lem1103138 _25376 h1) (fun h1 : (term5 _25376) = (@List.In _25376) => @lem1103140 _25376 h1)). Qed.
Lemma lem1103144 {_25376 : Type'} : (term5 _25376) = (@List.In _25376).
Proof. exact (EQ_MP (@lem1103141 _25376) (@lem1103131 _25376)). Qed.
Lemma lem1103145 {_25376 : Type'} : (term5 _25376) = (@List.In _25376).
Proof. exact (@lem1103144 _25376). Qed.
Lemma lem1103146 {_25376 : Type'} (x : _25376) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1103147 {_25376 : Type'} (x : _25376) : (term6 _25376 x) = (@List.In _25376 x).
Proof. exact (MK_COMB (@lem1103145 _25376) (@lem1103146 _25376 x)). Qed.
Lemma lem1103148 {_25376 : Type'} : (@nil _25376) = (@nil _25376).
Proof. exact (eq_refl (@nil _25376)). Qed.
Lemma lem1103149 {_25376 : Type'} (x : _25376) : (term7 _25376 x) = (@List.In _25376 x (@nil _25376)).
Proof. exact (MK_COMB (@lem1103147 _25376 x) (@lem1103148 _25376)). Qed.
Lemma lem1103150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1103151 {_25376 : Type'} (x : _25376) : (term8 _25376 x) = (term9 _25376 x).
Proof. exact (MK_COMB (@lem1103150) (@lem1103149 _25376 x)). Qed.
Lemma lem1103152 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1103153 {_25376 : Type'} (x : _25376) : ((term7 _25376 x) = False) = ((@List.In _25376 x (@nil _25376)) = False).
Proof. exact (MK_COMB (@lem1103151 _25376 x) (@lem1103152)). Qed.
Lemma lem1103154 {_25376 : Type'} : (term10 _25376) = (term11 _25376).
Proof. exact (fun_ext (fun x : _25376 => @lem1103153 _25376 x)). Qed.
Lemma lem1103155 {_25376 : Type'} : (@all _25376) = (@all _25376).
Proof. exact (eq_refl (@all _25376)). Qed.
Lemma lem1103156 {_25376 : Type'} : (term12 _25376) = (term13 _25376).
Proof. exact (MK_COMB (@lem1103155 _25376) (@lem1103154 _25376)). Qed.
Lemma lem1103157 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1103158 {_25376 : Type'} : (term14 _25376) = (term15 _25376).
Proof. exact (MK_COMB (@lem1103157) (@lem1103156 _25376)). Qed.
Lemma lem1103160 {_25376 : Type'} : (term5 _25376) = (@List.In _25376).
Proof. exact (EQ_MP (@lem1103141 _25376) (@lem1103131 _25376)). Qed.
Lemma lem1103161 {_25376 : Type'} : (term5 _25376) = (@List.In _25376).
Proof. exact (@lem1103160 _25376). Qed.
Lemma lem1103162 {_25376 : Type'} (x : _25376) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1103163 {_25376 : Type'} (x : _25376) : (term6 _25376 x) = (@List.In _25376 x).
Proof. exact (MK_COMB (@lem1103161 _25376) (@lem1103162 _25376 x)). Qed.
Lemma lem1103164 {_25376 : Type'} (h : _25376) (t : list _25376) : (@cons _25376 h t) = (@cons _25376 h t).
Proof. exact (eq_refl (@cons _25376 h t)). Qed.
Lemma lem1103165 {_25376 : Type'} (x : _25376) (h : _25376) (t : list _25376) : (term16 _25376 x h t) = (term17 _25376 x h t).
Proof. exact (MK_COMB (@lem1103163 _25376 x) (@lem1103164 _25376 h t)). Qed.
Lemma lem1103166 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1103167 {_25376 : Type'} (x : _25376) (h : _25376) (t : list _25376) : (term18 _25376 x h t) = (term19 _25376 x h t).
Proof. exact (MK_COMB (@lem1103166) (@lem1103165 _25376 x h t)). Qed.
Lemma lem1103169 {_25376 : Type'} : (term5 _25376) = (@List.In _25376).
Proof. exact (EQ_MP (@lem1103141 _25376) (@lem1103131 _25376)). Qed.
Lemma lem1103170 {_25376 : Type'} : (term5 _25376) = (@List.In _25376).
Proof. exact (@lem1103169 _25376). Qed.
Lemma lem1103171 {_25376 : Type'} (x : _25376) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1103172 {_25376 : Type'} (x : _25376) : (term6 _25376 x) = (@List.In _25376 x).
Proof. exact (MK_COMB (@lem1103170 _25376) (@lem1103171 _25376 x)). Qed.
Lemma lem1103173 {_25376 : Type'} (t : list _25376) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1103174 {_25376 : Type'} (x : _25376) (t : list _25376) : (term20 _25376 x t) = (@List.In _25376 x t).
Proof. exact (MK_COMB (@lem1103172 _25376 x) (@lem1103173 _25376 t)). Qed.
Lemma lem1103175 {_25376 : Type'} (x : _25376) (h : _25376) : (term21 _25376 x h) = (term21 _25376 x h).
Proof. exact (eq_refl (term21 _25376 x h)). Qed.
Lemma lem1103176 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term22 _25376 h x t) = (term23 _25376 h x t).
Proof. exact (MK_COMB (@lem1103175 _25376 x h) (@lem1103174 _25376 x t)). Qed.
Lemma lem1103177 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : ((term16 _25376 x h t) = (term22 _25376 h x t)) = ((term17 _25376 x h t) = (term23 _25376 h x t)).
Proof. exact (MK_COMB (@lem1103167 _25376 x h t) (@lem1103176 _25376 h x t)). Qed.
Lemma lem1103178 {_25376 : Type'} (h : _25376) (x : _25376) : (term24 _25376 h x) = (term25 _25376 h x).
Proof. exact (fun_ext (fun t : list _25376 => @lem1103177 _25376 h x t)). Qed.
Lemma lem1103179 {_25376 : Type'} : (@all (list _25376)) = (@all (list _25376)).
Proof. exact (eq_refl (@all (list _25376))). Qed.
Lemma lem1103180 {_25376 : Type'} (h : _25376) (x : _25376) : (term26 _25376 h x) = (term27 _25376 h x).
Proof. exact (MK_COMB (@lem1103179 _25376) (@lem1103178 _25376 h x)). Qed.
Lemma lem1103181 {_25376 : Type'} (h : _25376) : (term28 _25376 h) = (term29 _25376 h).
Proof. exact (fun_ext (fun x : _25376 => @lem1103180 _25376 h x)). Qed.
Lemma lem1103182 {_25376 : Type'} : (@all _25376) = (@all _25376).
Proof. exact (eq_refl (@all _25376)). Qed.
Lemma lem1103183 {_25376 : Type'} (h : _25376) : (term30 _25376 h) = (term31 _25376 h).
Proof. exact (MK_COMB (@lem1103182 _25376) (@lem1103181 _25376 h)). Qed.
Lemma lem1103184 {_25376 : Type'} : (term32 _25376) = (term33 _25376).
Proof. exact (fun_ext (fun h : _25376 => @lem1103183 _25376 h)). Qed.
Lemma lem1103185 {_25376 : Type'} : (@all _25376) = (@all _25376).
Proof. exact (eq_refl (@all _25376)). Qed.
Lemma lem1103186 {_25376 : Type'} : (term34 _25376) = (term35 _25376).
Proof. exact (MK_COMB (@lem1103185 _25376) (@lem1103184 _25376)). Qed.
Lemma lem1103187 {_25376 : Type'} : (term4 _25376) = (term36 _25376).
Proof. exact (MK_COMB (@lem1103158 _25376) (@lem1103186 _25376)). Qed.
Lemma lem1103188 {_25376 : Type'} : term36 _25376.
Proof. exact (EQ_MP (@lem1103187 _25376) (@lem1103136 _25376)). Qed.
