# Without quantifiers

#   Resolution
#   step = ["res", index, index]
#   clause = [lit, lit, ...]

#   RUP/DRUP/RAT/DRAT
#   step = ["add", clause] # guess whether RUP or RAT
#   step = ["rup", clause]
#   step = ["rat", clause, literal] # only RAT, DRAT
#   step = ["delete", clause]  # only DRUP, DRAT
#   clause = [lit, lit, ...]

#   LRAT
#   step = ["rup", clause, propagation_indices]
#   step = ["rat", clause, literal,
#           [[resolve_index, propagation_indices],
#            [resolve_index, propagation_indices]]]
#   clause = [lit, lit, ...]

#   PR
#   step = ["add", clause, witness or None]
#   step = ["delete", clause_index]

#   See "PRuning Through Satisfaction" by Marijn J.H. Heule, Benjamin Kiesl, Martina Seidl, and Armin Biere
#   See "Short Proofs Without New Variables" by Marijn J.H. Heule, Benjamin Kiesl, and Armin Biere
#   See "What a Difference a Variable Makes" by Marijn J.H. Heule, and Armin Biere

# With quantifiers

#   See "On Unification of QBF Resolution-Based Calculi" by Olaf Beyersdorff, Leroy Chew, and Mikoláš Janota
#   See "Efficient Extraction of Skolem Functions from QRAT Proofs" by Marijn J.H. Heule
#   See "QRAT+: Generalizing QRAT by a More Powerful QBF Redundancy Property" by Florian Lonsing and Uwe Egly

#   Q-Resolution
#   step = ["res", index, index]
#   clause = [lit, lit, ...]

#   Long distance Q-Resolution
#   step = ["res", index, index]
#   clause = [(lit, has_star), (lit, has_star), ...]

#   ∀Exp+Res
#   step = ["axiom", index, assignment]
#   step = ["res", index, index]
#   clause = [(lit, assignment), (lit, assignment), ...]

#   IR(M)-Calc
#   step = ["res", index, index]
#   step = ["inst", index, assignment]
#   step = ["merge", index, assignment] # only IRM
#   clause = [(lit, assignment), (lit, assignment), ...]

#   QRAT
#   step = ["n1", clause, None]    # removal of RUP/AT clause
#   step = ["n2", clause, None]    # addition of RUP/AT clause
#   step = ["e1", clause, literal] # removal of RAT clause on E literal
#   step = ["e2", clause, literal] # addition of RAT clause on E literal
#   step = ["u1", clause, literal] # removal of RAT clause on A literal
#   step = ["u2", clause, literal] # addition of RAT clause on A literal
#   clause = [lit, lit, ...]

#   QRAT+
#   ???

#   QU-Resolution
#   ???

#   CP+∀red
#   ???


# Operations

#   check_res               OK
#   check_drat              OK
#   check_lrat

#   convert_res_to_drat     OK
#   convert_drat_to_lrat    OK
#   convert_pr_to_drat      OK

#   trim_res                OK
#   trim_drat

#   interpolant_res         OK
#   interpolant_drup

#   check_qres              OK
#   check_ldqres
#   check_aexpres           OK
#   check_ir                OK
#   check_irm
#   check_qrat
#   check_qratp

#   convert_qres_to_ldqres
#   convert_ldqres_to_qres  useful? 

#   convert_qres_to_ir      OK
#   convert_ldqres_to_irm
#   convert_aexpres_to_ir

#   convert_qres_to_qrat
#   convert_ldqres_to_qrat

#   skolem_qres
#   skolem_irm
#   skolem_qrat

#   dep_trv
#   dep_std
#   dep_rrs
#     see "Soundness of Q-resolution with dependency schemes" by Friedrich Slivovsky and Stefan Szeider



def cases_res(steps, c_res):
	for i, step in enumerate(steps):
		if step[0] == "res":
			if not c_res(i, step[1], step[2]):
				return False
		else:
			return False
	return True

def cases_drat(steps, c_add, c_rup, c_rat, c_delete):
	for i, step in enumerate(steps):
		#print(i, step)
		if step[0] == "add":
			if not c_add(i, step[1]):
				return False
		elif step[0] == "rup":
			if not c_rup(i, step[1]):
				return False
		elif step[0] == "rat" and c_rat:
			if not c_rat(i, step[1], step[2]):
				return False
		elif step[0] == "delete" and c_delete:
			if not c_delete(i, step[1]):
				return False
		else:
			return False
	return True

def cases_lrat(steps, c_rup, c_rat):
	for i, step in enumerate(steps):
		if step[0] == "rup":
			if not c_rup(i, step[1], step[2]):
				return False
		elif step[0] == "rat":
			if not c_rat(i, step[1], step[2], step[3]):
				return False
		else:
			return False
	return True

def cases_pr(steps, c_add, c_delete):
	for i, step in enumerate(steps):
		if step[0] == "add":
			if not c_add(i, step[1], step[2]):
				return False
		elif step[0] == "delete" and c_rat:
			if not c_delete(i, step[1]):
				return False
		else:
			return False
	return True

cases_qres = cases_res

def cases_aexpres(steps, c_axiom, c_res):
	for i, step in enumerate(steps):
		if step[0] == "axiom":
			if not c_axiom(i, step[1], step[2]):
				return False
		elif step[0] == "res":
			if not c_res(i, step[1], step[2]):
				return False
		else:
			return False
	return True

def cases_irm(steps, c_res, c_inst, c_merge):
	for i, step in enumerate(steps):
		if step[0] == "res":
			if not c_res(i, step[1], step[2]):
				return False
		elif step[0] == "inst":
			if not c_inst(i, step[1], step[2]):
				return False
		elif step[0] == "merge" and c_merge:
			if not c_merge(i, step[1], step[2]):
				return False
		else:
			return False
	return True

########

def resolve(ca, cb, onlylit):
	# does clause resolution or cube consensus (aka. cube resolution)
	#	assert isinstance(ca, frozenset), type(ca)
	#	assert isinstance(cb, frozenset), type(cb)
	la = {onlylit(litx) for litx in ca}
	lb = {-onlylit(litx) for litx in cb}
	pivot = la & lb
	if len(pivot) < 1: return None, None, False # doesn't resolve
	if len(pivot) > 1: return None, None, True  # tautology
	pa = None
	pb = None
	r = set()

	for litx in ca:
		if onlylit(litx) in pivot:
			pa = litx
		else:
			r.add(litx)

	for litx in cb:
		if -onlylit(litx) in pivot:
			pb = litx
		else:
			r.add(litx)

	return pa, pb, frozenset(r)

class Formula:
	def __init__(self):
		self.quant = []
		self.quantdep = []
		self.complement_quantdep = None
		self.clauses = []

	def calc_complement_quantdep(self):
		self.complement_quantdep = [
			[j for j, qd in enumerate(self.quantdep[i]) if i not in qd]
			if q == "A" and i > 0 else None
			for i, q in enumerate(self.quant)
		]

	def has_dependency_cycle_with_complement(self):
		if self.complement_quantdep is None:
			self.calc_complement_quantdep()

		alldeps = [qd or cqd for qd, cqd in zip(self.quantdep, self.complement_quantdep)]
		import networkx as nx # TODO: make our own dfs based cycle check
		g = nx.DiGraph((i, j) for i, dep in enumerate(alldeps) if i > 0 for j in dep)
		try:
			nx.algorithms.cycles.find_cycle(g, source=None, direction="original")
		except:
			return False
		return True

	def qsplit(self, clause):
		forall = [lit for lit in clause if self.quant[abs(lit)] == "A"]
		exists = [lit for lit in clause if self.quant[abs(lit)] == "E"]
		return forall, exists

	def depunion(self, lits):
		union = set()
		for lit in lits:
			union.update(self.quantdep[abs(lit)])
		return frozenset(union)

	def complement_depunion(self, lits):
		union = set()
		for lit in lits:
			union.update(self.complement_quantdep[abs(lit)])
		return frozenset(union)

	def check_solution(self, assignment):
		for clause in self.clauses:
			if not any(lit in assignment for lit in clause):
				return False
		return True

def check_res(formula, proof_res):
	res_clauses = _res_to_clausal_proof(formula, proof_res)
	if res_clauses is None:
		return False
	return len(res_clauses[-1]) == 0

def _res_to_clausal_proof(formula, proof_res):
	res_clauses = formula.clauses[:]

	def on_res(i, a, b):
		pa, pb, r = resolve(res_clauses[a], res_clauses[b], lambda l: l)
		if pa is None:
			#print("step {}, resolution of {} and {} failed".format(i, a, b))
			return False
		res_clauses.append(r)
		#print("res {} x {} → {}".format(res_clauses[a], res_clauses[b], r))
		return True

	if cases_res(proof_res, on_res):
		#print(res_clauses)
		return res_clauses
	else:
		return None

def trim_res(formula, proof_res):
	nc = len(formula.clauses)
	live = set()
	n = [nc+len(proof_res)-1]
	while n:
		x = n[-1]
		del n[-1]
		if x < nc or x in live:
			continue
		live.add(x)
		_res, a, b = proof_res[x-nc]
		n.append(a)
		n.append(b)
		n.sort()

	m = {i: i for i in range(nc)}
	nproof = []
	for i, (_res, a, b) in enumerate(proof_res):
		if i+nc in live:
			m[nc+i] = nc+len(nproof)
			nproof.append(("res", m[a], m[b]))
	return nproof

def interpolant_res(formula, proof_res, clause_colors):
	res_clauses = []
	var_colors = {}

	def or_node(*n):
		n = [i for i in n if i != False]
		if len(n) == 1:
			return n[0]
		elif len(n) > 1:
			return ("or",)+tuple(n)
		else:
			return False

	def and_node(*n):
		n = [i for i in n if i != True]
		if len(n) == 1:
			return n[0]
		elif len(n) > 1:
			return ("and",)+tuple(n)
		else:
			return True

	for clause, color in zip(formula.clauses, clause_colors):
		for lit in clause:
			var_colors.setdefault(abs(lit), set()).add(color)
	for clause, color in zip(formula.clauses, clause_colors):
		if color == 0:
			res_clauses.append((clause, or_node(*[lit for lit in clause if var_colors[abs(lit)]=={0, 1}])))
		elif color == 1:
			res_clauses.append((clause, True))
		else:
			assert False

	def on_res(i, a, b):
		ca, xa = res_clauses[a]
		cb, xb = res_clauses[b]
		pa, pb, r = resolve(ca, cb, lambda l: l)
		if pa is None:
			#print("step {}, resolution of {} and {} failed".format(i, ca, cb))
			return False
		pivot_color = var_colors[abs(pa)]
		if pivot_color == {0}:
			res_clauses.append((r, or_node(xa, xb)))
		else:
			res_clauses.append((r, and_node(xa, xb)))
		return True

	if cases_res(proof_res, on_res):
		#print(res_clauses)
		return res_clauses[-1][1]
	else:
		return False

def resolvents(formula, clause, literal):
	assert literal in clause
	for d in formula:
		if -literal in d:
			pa, pb, r = resolve(clause, d, lambda l: l)
			if r == True: continue # tautology
			if r == False: assert False
			yield r

def enum_resolvents(formula, clause, literal):
	assert literal in clause
	for i, d in enumerate(formula):
		if -literal in d:
			pa, pb, r = resolve(clause, d, lambda l: l)
			if r == True: continue # tautology
			if r == False: assert False
			yield i, r

def unit_propagate_(formula, initial_assignment):
	assignment = {}
	def unit_under_assignment(clause):
		a = 0
		for lit in clause:
			if lit > 0:
				t = assignment.get(lit, 0)
			else:
				t = -assignment.get(-lit, 0)
			if t == 1:
				return 0
			if t == 0:
				if a != 0:
					return 0
				a = lit
		return a

	initial_assignment = tuple(initial_assignment)

	reason = {l: -1 for l in initial_assignment}
	seen = {-1}
	hints = []
	def reason_dfs(ci, x):
		if ci in seen:
			return
		seen.add(ci)
		c = tuple(formula[ci])
		#print(ci, c, [reason.get(-lit, None) for lit in c], "excused=", x)
		for lit in c:
			if lit != x:
				reason_dfs(reason[-lit], -lit)
		hints.append(ci)

	queue = set(initial_assignment)
	#print(queue)
	while queue:
		a = queue.pop()
		#print(" unit prop", a)
		k = 1 if a > 0 else -1
		assignment[abs(a)] = k
		for i, clause in enumerate(formula): # terrible performance
			a2 = unit_under_assignment(clause)
			if a2:
				if a2 not in reason:
					#print(" reason[{}] = {} {}".format(a2, i, tuple(clause)))
					reason[a2] = i
				if -a2 in reason:
					#print("reason =", reason)
					reason_dfs(reason[a2], a2)
					reason_dfs(reason[-a2], -a2)
					#print("unsat", hints)
					return False, hints

				queue.add(a2)

	#print("sat")
	return True, [k*v for k, v in assignment.items()]

def unit_propagate(formula, initial_assignment):
	sat, assignment_or_hints = unit_propagate_(formula, initial_assignment)
	if sat:
		return assignment_or_hints

def units_of_formula(formula):
	for clause in formula:
		if len(clause) == 1:
			unit, = clause
			yield unit

def check_drat(formula, proof_drat):
	proof = check_drat_2(formula, proof_drat, generate_lrat=False)
	return proof is not None

def convert_drat_to_lrat(formula, proof_drat):
	return check_drat_2(formula, proof_drat, generate_lrat=True)

def check_drat_2(formula, proof_drat, generate_lrat):

	formula = [frozenset(clause) for clause in formula.clauses[:]]
	lrat = []

	def on_add(i, clause):
		if on_rup(i, clause): return True
		for j in range(len(clause)): # try every pivot
			if on_rat(i, clause, clause[j]): return True
		return False

	def on_rup(i, clause):
		assignment_falsifying_clause = [-a for a in clause]
		sat, hints = unit_propagate_(formula, assignment_falsifying_clause)
		if sat:
			#print("rup addition of", clause, "failed")
			return False
		formula.append(frozenset(clause))
		lrat.append(["rup", clause, hints])
		return True

	def on_rat(i, clause, literal):
		#print([list(c) for c in formula], clause, literal)
		rhints = []
		for ci, r in enum_resolvents(formula, clause, literal):
			assignment_falsifying_resolvent = [-a for a in r]
			sat, hints = unit_propagate_(formula, assignment_falsifying_resolvent)
			if sat:
				#print("rat addition of", clause, "failed because of resolvent", r)
				return False
			rhints.append([ci, hints])
		#print("rat addition of", clause, "succeeded")
		formula.append(frozenset(clause))
		lrat.append(["rat", clause, literal, rhints])
		return True

	def on_delete(i, clause):
		if generate_lrat:
			return True
		nonlocal formula
		n = len(formula)
		zclause = frozenset(clause)
		formula = [c for c in formula if c != zclause]
		return True

	if cases_drat(proof_drat, on_add, on_rup, on_rat, on_delete):
		#print("final formula=", [list(c) for c in formula])

		if frozenset() in formula:
			return lrat
		sat, hints = unit_propagate_(formula, units_of_formula(formula))
		if not sat:
			lrat.append(["rup", [], hints])
			return lrat
		return None
	else:
		return None

def convert_res_to_drat(formula, proof_res):
	res_clauses = _res_to_clausal_proof(formula, proof_res)
	del res_clauses[:len(formula.clauses)]
	return [("add", clause) for clause in res_clauses]

def convert_pr_to_drat(formula, proof_pr): 
	# TODO
	formula = formula.clauses[:]
	proof_drat = []
	x = 99999999

	def on_add(i, clause, witness):
		clause = tuple(clause)
		c = set(clause)
		w = witness and set(witness)

		if not witness:
			proof_drat.append(("rup", clause))

		elif len(c) == len(w) and len(c)-1 == len(c&w):
			# witness differs in one literal which is moved to first position
			proof_drat.append(("rat", tuple(c-w) + tuple(c&w)))

		else:
			sat_by_witness = []
			red_by_witness = []
			for fclause in formula:
				if any(-lit in witness for lit in fclause):
					# witness satisfies
					sat_by_witness.append(tuple(fclause))
				else:
					reduced = tuple(lit for lit in fclause if lit not in witness)
					if len(reduced) > 0:
						red_by_witness.append(reduced)
				
			# 1
			for fclause in red_by_witness:
				proof_drat.append(("add", (-x,) + tuple(fclause)))

			# 2
			for lit in witness:
				proof_drat.append(("add", (-x, lit)))

			for fclause in sat_by_witness:
				proof_drat.append(("add", (x,) + fclause))
				proof_drat.append(("delete", fclause))

			for lit in witness:
				proof_drat.append(("delete", (lit, -x)))

			# 3
			proof_drat.append(("add", (x,) + clause))

			# 4
			for lit in witness:
				proof_drat.append(("add", (lit, -x)))

			for fclause in sat_by_witness + [clause]:
				proof_drat.append(("add", fclause))
				proof_drat.append(("delete", (x,) + fclause))

			for lit in witness:
				proof_drat.append(("delete", (-x, lit)))

			# 5
			for fclause in red_by_witness:
				proof_drat.append(("delete", (-x,) + tuple(fclause)))

		formula.append(clause)
		return True

	def on_delete(i, clause):
		nonlocal formula
		proof_drat.append(("delete", clause))
		formula = [fclause for fclause in formula if set(clause) != set(fclause)]
		return True

	if cases_pr(proof_pr, on_add, on_delete):
		#print(proof_pr)
		return proof_drat
	else:
		return None

def vsplit(clause, vars):
	has   = [lit for lit in clause if abs(lit) in vars]
	hasnt = [lit for lit in clause if abs(lit) not in vars]
	return has, hasnt

def a_reduction(formula, clause):
	# from a clause remove all forall quantified literals
	# that no exists quantified literals depend on

	# example:
	# formula.quant    = ["X",  "A",  "E", "A" ]
	# formula.quantdep = [None, None, [1], None]
	# clause           = [1, 2, 3]
	# returns          = [1, 2], [3]

	# reasoning: the A-literal can't be relied on to satisfy the clause,
	# because the E-literals can't take over in the case the A-literal is false,
	# because they can't depend on the A-literal

	forall, exists     = formula.qsplit(clause)
	exdeps             = formula.depunion(exists)
	forall_d, forall_u = vsplit(forall, exdeps)

	return (exists + forall_d)

def e_reduction(formula, cube):
	# from a cube remove all exists quantified literals
	# that no forall quantified literals depend on
	forall, exists     = formula.qsplit(cube)
	fadeps             = formula.complement_depunion(forall)
	exists_d, exists_u = vsplit(exists, fadeps)
	return (forall + exists_d)


def negmap(clause):
	assignment = frozenset(-lit for lit in clause)
	return assignment

def check_qres(formula, proof_qres, original_formula=None):
	# For UNSAT proofs (original_formula is None)
	#  0: clause from formula
	#  1: clause from formula
	#  ...
	#  8: clause q-resolution (applies a-reduction)
	#  9: clause q-resolution (applies a-reduction)

	# For SAT proofs (original_formula is not None)
	#  0: cube that is solution to formula
	#  1: cube that is solution to formula
	#  ...
	#  8: cube q-consensus (applies e-reduction)
	#  9: cube q-consensus (applies e-reduction)

	# For SAT proofs the following extra checks are necessary
	# for each leaf (which is a cube/assignment)
	#    evaluate original formula under the assignment
	#      simplifies to true -> good, continue
	#      else -> remove all forall quantified literals, SAT solve it
	#        SAT -> good, continue
	#        UNSAT -> error

	if original_formula:
		# we start with cubes that are solutions of the original formula

		cubes = formula.clauses # lol
		of = Formula()
		of.clauses = original_formula
		for cube in cubes:
			if not of.check_solution(cube):
				# print("initial cube not a solution", cube)
				# TODO
				return False

		if formula.has_dependency_cycle_with_complement():
			# print("in certain DQBF skolem functions cannot be derived from the proof of the complement")
			# TODO
			return False
		reduction = e_reduction
		resolve_on = "A"
	else:
		# we start with clauses of the original formula
		reduction = a_reduction
		resolve_on = "E"

	qres_clauses = formula.clauses[:]

	def on_qres(i, a, b):
		ca = reduction(formula, qres_clauses[a])
		cb = reduction(formula, qres_clauses[b])
		pa, pb, r = resolve(ca, cb, lambda l: l)
		if pa is None:
			#print("step {}, resolution of {} and {} failed".format(i, ca, cb))
			return False
		if formula.quant[abs(pa)] != resolve_on:
			#print("step {}, pivot {} not on {}-quantified variable".format(i, abs(pa), resolve_on))
			return False
		rr = reduction(formula, r)
		qres_clauses.append(rr)
		#print("qres {} x {} → {}".format(qres_clauses[a], qres_clauses[b], rr))
		#print(" after forall reduction {} x {}".format(ca, cb))
		return True

	if cases_qres(proof_qres, on_qres):
		#print(qres_clauses)
		return len(qres_clauses[-1]) == 0
	else:
		return False

def check_aexpres(formula, proof_aexpres):
	nf = []
	np = []
	nv = {}

	def on_axiom(i, index, assignment):
		c = formula.clauses[index]
		nc = []
		for lit in c:
			v = abs(lit)
			q = formula.quant[v]
			if q == "E":
				tnlit = (v,) + tuple(assignment[dep] for dep in formula.quantdep[v])
				nva = nv.setdefault(tnlit, len(nv))
				nlit = nva if lit > 0 else -nva
				nc.append(nlit)
			elif q == "A":
				if lit > 0 and assignment[v]:
					# tautology
					nc = None
					break
		nf.append(nc)
		return True

	def on_res(i, a, b):
		np.append(["res", a, b])
		return True

	if cases_aexpres(proof_aexpres, on_axiom, on_res):
		nfo = Formula()
		nfo.clauses = nf
		#print("converted aexpres proof to res proof")
		#from pprint import pprint
		#pprint(nv)
		#pprint(nf)
		#pprint(np)
		return check_res(nfo, np)
	else:
		return False


def _repr_ir(c):
	return "("+(" ".join("{}={}".format(lit, list(lassign)) for lit, lassign in c))+")"

def _over_ir(a, b, v):
	return frozenset(a | {l for l in b if -l not in a and abs(l) in v})

def check_ir(formula, proof_ir):
	ir_clauses = []

	for i, clause in enumerate(formula.clauses):
		c_forall, c_exists = formula.qsplit(clause)
		a_forall = negmap(c_forall)
		ir_clause = tuple((lit, frozenset(-d for d in c_forall if abs(d) in formula.quantdep[abs(lit)])) for lit in c_exists)
		ir_clauses.append(ir_clause)

	def inst(clause, nassign):
		if not nassign:
			return clause
		return frozenset((lit, _over_ir(lassign, nassign, formula.quantdep[abs(lit)])) for lit, lassign in clause)

	def on_res(i, a, b):
		pa, pb, ir = resolve(ir_clauses[a], ir_clauses[b], lambda l: l[0])
		if pa is None:
			return False
		if pa[1] != pb[1]:
			return False
		ir_clauses.append(ir)
		#print("res", _repr_ir(ir))
		return True

	def on_inst(i, node, assign):
		ir = inst(ir_clauses[node], assign)
		ir_clauses.append(ir)
		#print("inst", _repr_ir(ir))
		return True

	if cases_irm(proof_ir, on_res, on_inst, None):
		return len(ir_clauses[-1]) == 0

def convert_qres_to_ir(formula, proof_qres):
	indexmap_qres_ir = {}
	proof_ir = []

	qres_clauses = []
	ir_clauses = []

	for i, clause in enumerate(formula.clauses):
		c_forall, c_exists = formula.qsplit(clause)
		a_forall = negmap(c_forall)
		ir_clause = tuple((lit, frozenset(-d for d in c_forall if abs(d) in formula.quantdep[abs(lit)])) for lit in c_exists)

		qres_clauses.append(clause)
		indexmap_qres_ir[i] = i
		ir_clauses.append(ir_clause)

	def lazy_inst(irnode, nassign):
		if not nassign:
			return irnode
		clause = ir_clauses[irnode]
		nclause = frozenset((lit, _over_ir(lassign, nassign, formula.quantdep[abs(lit)])) for lit, lassign in clause)
		if clause != nclause:
			proof_ir.append(("inst", irnode, nassign))
			ir_clauses.append(nclause)
			return len(ir_clauses)-1
		return irnode

	def on_qres(i, a, b):
		ia = indexmap_qres_ir[a]
		ib = indexmap_qres_ir[b]
		ca = a_reduction(formula, qres_clauses[a])
		cb = a_reduction(formula, qres_clauses[b])
		pa, pb, r = resolve(ca, cb, lambda l: l)
		if pa is None:
			#print("step {}, resolution of {} and {} failed", i, ca, cb)
			return False
		rr = a_reduction(formula, r)
		qres_clauses.append(rr)
		#print("qres {} x {} → {}".format(qres_clauses[a], qres_clauses[b], rr))
		#print(" after forall reduction {} x {}".format(ca, cb))

		ipa, ipb, _ = resolve(ir_clauses[ia], ir_clauses[ib], lambda l: l[0])
		ia = lazy_inst(ia, ipb[1])
		ib = lazy_inst(ib, ipa[1])
		_, _, ir = resolve(ir_clauses[ia], ir_clauses[ib], lambda l: l[0]) # welp
		proof_ir.append(("res", ia, ib))
		ir_clauses.append(ir)
		# print("ir {} x {} → {}".format(
		# 	_repr_ir(ir_clauses[ia]),
		# 	_repr_ir(ir_clauses[ib]),
		# 	_repr_ir(ir)))
		ic = len(ir_clauses) - 1
		any_assignments = set()
		for (lit, lassign) in ir_clauses[ic]:
			any_assignments.update(lassign)
		ic = lazy_inst(ic, any_assignments)
		indexmap_qres_ir[i + len(formula.clauses)] = ic
		return True

	if cases_qres(proof_qres, on_qres):
		return proof_ir

def skolem_qres(formula, proof_qres, sat):
	qres_clauses = formula.clauses[:]

	if sat:
		reduction = e_reduction
	else:
		reduction = a_reduction

	reduced_at_node = {}
	pivot_at_node = {}
	antecedents = {}

	for i, cc in enumerate(qres_clauses):
		rcc = reduction(formula, cc)
		qres_clauses[i] = rcc
		reduced_at_node[i] = set(cc)-set(rcc)

	def on_qres(i, a, b):
		# everything reduced up-front
		# ca = a_reduction(formula, qres_clauses[a])
		# cb = a_reduction(formula, qres_clauses[b])
		ca = qres_clauses[a]
		cb = qres_clauses[b]
		pa, pb, r = resolve(ca, cb, lambda l: l)
		if pa is None:
			return False
		rr = reduction(formula, r)
		reduced_at_node[len(qres_clauses)] = set(r)-set(rr)
		pivot_at_node[len(qres_clauses)] = pa
		antecedents[len(qres_clauses)] = (a, b)
		qres_clauses.append(rr)
		return True

	if not cases_qres(proof_qres, on_qres):
		return

	seen = set()
	topo = []
	def visit(n):
		if n in seen: return
		for a in antecedents.get(n, []):
			visit(a)
		topo.append(n)
	visit(len(qres_clauses)-1)

	expr = {}

	for n in reversed(topo):
		for l in reduced_at_node.get(n, []):
			v = abs(l)
			if v not in expr:
				expr[v] = True if l > 0 else False
			elif l > 0:
				q = ("and",) + tuple(-l for l in qres_clauses[n])
				expr[v] = ("or", expr[v], q)
			else:
				q = ("or",) + tuple(qres_clauses[n])
				expr[v] = ("and", expr[v], q)

	return expr

def test():
	from pprint import pprint

	f0 = Formula()
	f0.clauses = [[-1, -2, -3], [1], [2], [3]]
	f0_res = [
		# 0: initial [-1, -2, -3],
		# 1: initial [1],
		# 2: initial [2],
		# 3: initial [3],
		["res", 0, 1], # 4: [-2, -3]
		["res", 0, 3], # 5: [-1, 2] (superflous)
		["res", 4, 2], # 6: [-3]
		["res", 6, 3], # 7: []
	]

	f1 = Formula()
	f1.quant = "XEA"
	f1.quantdep = [None, [], None]
	f1.clauses = [[1, 2], [-1, -2]]

	f1_qres = [
		# 0: initial [1, 2],
		# 1: initial [-1, -2],
		["res", 0, 1] # 2
	]

	f2 = Formula()
	f2.quant = "XEAEEAEE"
	f2.quantdep = [None, [], [], [2], [2], [], [2, 5], [2, 5]]
	f2.clauses = [
		[-1, -7],
		[ 2,  6,  7],
		[ 3, -5, -6],
		[ 4, -5, -6],
		[-3, -4,  5],
		[ 1,  6]
	]

	f2_qres = [
		# 0: initial [-1, -7],
		# 1: initial [ 2,  6,  7],
		# 2: initial [ 3, -5, -6],
		# 3: initial [ 4, -5, -6],
		# 4: initial [-3, -4,  5],
		# 5: initial [ 1,  6],
		["res", 3, 4], # 6: [-3, -5, -6]
		["res", 2, 6], # 7: [-5, -6]
		["res", 1, 7], # 8: [2, -5, 7]
		["res", 5, 7], # 9: [1, -5]
		["res", 0, 8], # 10: [-1, 2, -5]
		["res", 9, 10] # 11: []
	]

	f2_aexpres = [
		["axiom", 4, {2: False, 5: False}], # 0: [-3f, -4f]
		["axiom", 0, {2: False, 5: True}],  # 1: [-1,  -7ft]
		["axiom", 1, {2: False, 5: True}],  # 2: [ 6ft, 7ft]
		["axiom", 2, {2: False, 5: True}],  # 3: [ 3f, -6ft]
		["axiom", 3, {2: False, 5: True}],  # 4: [ 4f, -6ft]
		["axiom", 5, {2: False, 5: True}],  # 5: [ 1,   6ft]
		["res", 0, 3],
		["res", 6, 4],
		["res", 1, 2],
		["res", 8, 5],
		["res", 7, 9],
	]

	f3 = Formula()
	f3.clauses = [[1], [-1, 2], [-2, 3], [-3]]
	f3_res = [
		# 0: initial [1],
		# 1: initial [-1, 2],
		# 2: initial [-2, 3],
		# 3: initial [-3],
		["res", 0, 1], # 4: [2]
		["res", 2, 3], # 5: [-2]
		["res", 4, 5], # 6: []
	]

	f4 = Formula()
	f4.clauses = [
		[ 1,  2, -3], 
		[-1, -2,  3], 
		[ 2,  3, -4], 
		[-2, -3,  4], 
		[-1, -3, -4], 
		[ 1,  3,  4], 
		[-1,  2,  4], 
		[ 1, -2, -4],
	]
	f4_drat = [
		["add", [-1]],
		["delete", [-1, -2,  3]],
		["delete", [-1, -3, -4]],
		["delete", [-1,  2,  4]],
		["add", [2]]
		# by the end unit propagating the two
		# units -1 and 2 in the formula leads
		# to a conflict
	]

	php2 = Formula()
	php2.clauses = [
		[1, 4], [2, 5], [3, 6],
		[-1, -2], [-1, -3], [-2, -3],
		[-4, -5], [-4, -6], [-5, -6]
	]
	php2_pr = [
		["add", [-2, -4], [2, 4, -1, -5]],
		["add", [-4], None]
	]

	f5 = Formula()
	f5.quant = "XAE"
	f5.quantdep = [None, [], [1]]
	f5.clauses = [[1, 2], [-1, -2]]
	f5_original_clauses = [[1, -2], [-1, 2]]

	f5_qres = [
		# 0: initial [1, 2],
		# 1: initial [-1, -2],
		["res", 0, 1] # 2
	]

	def damage_qres(f, qres):
		for i in range(len(qres)):
			qres_broken = qres[:]
			qres_step_broken = qres_broken[i][:]
			if qres_step_broken[1] > 0:
				qres_step_broken[1] -= 1
			elif qres_step_broken[2] > 0:
				qres_step_broken[2] -= 1
			else:
				continue
			qres_broken[i] = qres_step_broken

			if check_qres(f, qres_broken):
				return False
		return True

	assert not check_res(f0, [])
	assert not check_qres(f1, [])
	assert not check_drat(f4, [])
	assert not check_drat(php2, [])

	assert check_res(f0, f0_res)
	assert check_res(f0, trim_res(f0, f0_res))

	assert check_qres(f1, f1_qres)
	assert damage_qres(f1, f1_qres)
	assert not check_res(f1, f1_qres)
	f1_ir = convert_qres_to_ir(f1, f1_qres)
	pprint(f1_ir)
	assert check_ir(f1, f1_ir)
	print()


	assert check_qres(f2, f2_qres)
	assert damage_qres(f2, f2_qres)
	assert not check_res(f2, f2_qres)
	f2_ir = convert_qres_to_ir(f2, f2_qres)
	pprint(f2_ir)
	assert check_ir(f2, f2_ir)
	print()

	assert check_aexpres(f2, f2_aexpres)

	assert check_res(f3, f3_res)
	assert check_res(f3, trim_res(f3, f3_res))
	r = interpolant_res(f3, f3_res, [0, 0, 1, 1])
	print("interpolant =", repr(r))
	print()

	assert check_drat(f4, f4_drat)
	f4_lrat = convert_drat_to_lrat(f4, f4_drat)
	pprint(f4.clauses)
	pprint(f4_lrat)

	php2_drat = convert_pr_to_drat(php2, php2_pr)
	pprint(php2_drat)
	assert check_drat(php2, php2_drat)

	assert check_qres(f5, f5_qres, f5_original_clauses)
	skolems = skolem_qres(f5, f5_qres, True)
	for (n, sk) in skolems.items():
		print(" e{} = {}".format(n, sk))

if __name__ == '__main__':
	test()
