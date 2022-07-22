import data.real.basic
import group_theory.finiteness
import algebra.group.defs

noncomputable theory

open set
open group
open subgroup
open add_group

variables {G : Type*} [add_comm_group G]

-- Let G be a group and S the set of representants of G/mG
def fin_quotient (S : set G) [finite S] (m : ℕ):= -- m ≥ 2
  ∀ g : G, ∃ g₀ ∈ S, ∃ h : G, g = g₀ + m•h

-- Heights formulated with a general m
class height (ht : G → ℝ) :=
-- (nonneg : ∀ g : G, 0 ≤ ht g)
(C₁ : G → ℝ)
(upper_bound : ∀ g₀ : G, ∀ g : G, ht(g₀ + g) ≤ 2*ht g  + C₁ g₀)
(m : ℕ) (Hm : m ≥ 2)
(C₂ : ℝ)
(lower_bound : ∀ g : G, ht (m•g) ≥ (m^2)*(ht g) + C₂)
(finite_boxes : ∀ C₃ : ℝ, {g : G | ht g ≤ C₃}.finite)

-- Lemma ?
-- Obtenir les C's de cada Q i definir C₂ de l'altura ht ??? 
-- També volem heredar les hipotesis


variables (ht : G → ℝ) [height ht]
variables {S : set G} [finite S] 

-- let C := max{C₁ Q | Q : S} + C₂
def C [fintype S] (hS : S.nonempty) (h : fin_quotient S (height.m ht)) : ℝ :=
  ((height.C₁ ht ''S).to_finset.max' (set.nonempty.image (height.C₁ ht) hS)) + height.C₂ ht


#check height.C₁ ht 

lemma useful_C (hS : nonempty S.to_finset) (h : fin_quotient S (height.m ht)) (g₀ : S) (g : G):
(ht (g - g₀) ≤ ht (2•g) + C)
:=
begin
  sorry
end

#check useful_C

lemma useful_C' (h : fin_quotient S (height.m ht)) (g₀ : S) (g : G) :
(∀ g : G, ht ((height.m ht)•g) ≥ ((height.m ht)^2)*(ht g) + (height.C₁ ht ''S).to_finset.max + height.C₂ ht)
:=
begin
  sorry
end

-- Descent theorem
lemma main_theorem (S : set G) [finite S] (m : ℕ) (Hm : m ≥ 2) (h : fin_quotient S m) 
(ht : G → ℝ) [height ht] : 
fg G :=
begin
  fconstructor,
  fconstructor,
  
  -- Usar el lema usefull_C per obtenir la C
  -- Donar el subconjunt generador S ∪ {g : G | ht g ≤ C} (per propietats és finit)
  -- A partir d'aquí no entenc com funciona...
  -- Donat un P
  -- Definim la seq. {P_j} (amb les seves definicions/hipotesis) 
  -- Veiem que dins de la seq. hi ha elements d'altura ≤ C
  -- Escrivim P com a combinació de Qᵢ i algun Pⱼ
  -- Ho usem pel Pⱼ que té altura ≤ C
  
  sorry,
end
















