import sys
import re
sys.path.append("llvmlite")
from llvmlite import ir

class Builder:
	def __init__(self, nodes, sorts, builder):
		self.nodes = nodes
		self.sorts = sorts
		self.builder = builder

	def op_sext(self, args, name):
		ty = ir.IntType(args[0].type.width + args[1])
		return self.builder.sext(args[0], ty, name)


	def op_uext(self, args, name):
		ty = ir.IntType(args[0].type.width + args[1])
		return self.builder.zext(args[0], ty, name)


	def op_slice(self, args, name):
		v = args[0]
		n = args[0].type.width
		u = args[1]+1
		l = args[2]
		if l > 0:
			v = self.builder.lshr(v, ir.Constant(v.type, l))
			u -= l
		if u < v.type.width:
			v = self.builder.trunc(v, ir.IntType(u))
		return v

	########


	def op_not(self, args, name):
		return self.builder.not_(args[0], name)


	def op_inc(self, args, name):
		return self.builder.add(args[0], ir.Constant(args[0].type, 1), name)


	def op_dec(self, args, name):
		return self.builder.sub(args[0], ir.Constant(args[0].type, 1), name)


	def op_neg(self, args, name):
		return self.builder.neg(args[0], name)


	def op_redand(self, args, name):
		ones = ir.Constant(args[0].type, (1 << args[0].type.width)-1)
		return self.builder.icmp_unsigned("==", args[0], ones, name)


	def op_redor(self, args, name):
		zero = ir.Constant(args[0].type, 0)
		return self.builder.icmp_unsigned("!=", args[0], zero, name)


	def op_redxor(self, args, name):
		pass

	########


	def op_iff(self, args, name):
		return self.builder.icmp_unsigned("==", args[0], args[1], name)


	def op_implies(self, args, name):
		return self.builder.or_(self.builder.not_(args[0]), args[1], name)


	def op_eq(self, args, name):
		return self.builder.icmp_unsigned("==", args[0], args[1], name)


	def op_ne(self, args, name):
		return self.builder.icmp_unsigned("!=", args[0], args[1], name)

	########


	def op_sgt(self, args, name):
		return self.builder.icmp_signed(">", args[0], args[1], name)


	def op_sgte(self, args, name):
		return self.builder.icmp_signed(">=", args[0], args[1], name)


	def op_slt(self, args, name):
		return self.builder.icmp_signed("<", args[0], args[1], name)


	def op_slte(self, args, name):
		return self.builder.icmp_signed("<=", args[0], args[1], name)

	########


	def op_ugt(self, args, name):
		return self.builder.icmp_unsigned(">", args[0], args[1], name)


	def op_ugte(self, args, name):
		return self.builder.icmp_unsigned(">=", args[0], args[1], name)


	def op_ult(self, args, name):
		return self.builder.icmp_unsigned("<", args[0], args[1], name)


	def op_ulte(self, args, name):
		return self.builder.icmp_unsigned("<=", args[0], args[1], name)

	########


	def op_and(self, args, name):
		return self.builder.and_(args[0], args[1], name)


	def op_nand(self, args, name):
		return self.builder.not_(self.builder.and_(args[0], args[1]), name)


	def op_nor(self, args, name):
		return self.builder.not_(self.builder.or_(args[0], args[1]), name)


	def op_or(self, args, name):
		return self.builder.or_(args[0], args[1], name)


	def op_xnor(self, args, name):
		return self.builder.not_(self.builder.xor(args[0], args[1]), name)


	def op_xor(self, args, name):
		return self.builder.xor(args[0], args[1], name)

	########


	def op_rol(self, args, name):
		pass


	def op_ror(self, args, name):
		pass


	def op_sll(self, args, name):
		return self.build.shl(args[0], args[1], name)


	def op_sra(self, args, name):
		return self.build.ashr(args[0], args[1], name)


	def op_srl(self, args, name):
		return self.build.lshr(args[0], args[1], name)

	########


	def op_add(self, args, name):
		return self.builder.add(args[0], args[1], name)


	def op_mul(self, args, name):
		return self.builder.mul(args[0], args[1], name)


	def op_sdiv(self, args, name):
		pass


	def op_udiv(self, args, name):
		pass


	def op_smod(self, args, name):
		pass


	def op_srem(self, args, name):
		pass


	def op_urem(self, args, name):
		pass


	def op_sub(self, args, name):
		return self.builder.sub(args[0], args[1], name)

	########


	def op_saddo(self, args, name):
		pass


	def op_sdivo(self, args, name):
		pass


	def op_smulo(self, args, name):
		pass


	def op_ssubo(self, args, name):
		pass


	def op_uaddo(self, args, name):
		pass


	def op_udivo(self, args, name):
		pass


	def op_umulo(self, args, name):
		pass


	def op_usubo(self, args, name):
		pass


	########


	def op_concat(self, args, name):
		a = args[0]
		b = args[1]
		aw = a.type.width
		bw = b.type.width
		ty = ir.IntType(aw+bw)

		ax = self.builder.zext(a, ty)
		bx = self.builder.zext(b, ty)

		return self.builder.add(
			self.builder.shl(ax, ir.Constant(ax.type, bw)),
			bx,
			name)


	def op_read(self, args, name):
		pass


	def op_ite(self, args, name):
		return self.builder.select(args[0], args[1], args[2], name)


	def op_write(self, args, name):
		pass


def parse(btor2, module, name):

	nodes = {}
	sorts = {}

	whitespace = re.compile(r"\s+")
	lines = btor2.split("\n")
	lines = [line.split(";", 1)[0] for line in lines]
	inputs = []
	state = []
	state_index = {}

	todoops = set()

	for p in (0, 1):
		# pass 0: collect types
		# pass 1: build function

		if p == 1:
			state_ty = ir.global_context.get_identified_type(name+"_state")
			state_ty.set_body(*state)
			state_ptr_ty = ir.PointerType(state_ty)

			fnty = ir.FunctionType(ir.VoidType(), (state_ptr_ty, state_ptr_ty)+tuple(ty for i, ty, name in inputs))
			func = ir.Function(module, fnty, name=name)
			extra_args = [
				(-1, None, "state"),
				(-2, None, "state_next")
			]
			for arg, (i, _, name) in zip(func.args, extra_args+inputs):
				arg.name = name
				nodes[i] = arg

			state_ptr = nodes.pop(-1)
			state_next_ptr = nodes.pop(-2)

			# Now implement the function
			block = func.append_basic_block(name="entry")
			builder = ir.IRBuilder(block)
			#a, b = func.args
			#result = builder.fadd(a, b, name="res")

			bbuilder = Builder(nodes, sorts, builder)
			print(nodes)

		for line in lines:
			line = re.sub(whitespace, " ", line)
			line = line.strip()
			if not line:
				continue		
			def todo():
				print("todo:", line)
			tokens = line.split(" ")
			assert len(tokens) >= 2
			i = int(tokens[0])

			if tokens[1] == "sort":
				if p == 0:
					if tokens[2] == "bitvec":
						sorts[i] = ir.IntType(int(tokens[3]))
					elif tokens[2] == "array":
						index_ty = sorts[int(tokens[3])]
						elem_ty = sorts[int(tokens[4])]
						assert isinstance(index_ty, ir.IntType)
						sorts[i] = ir.ArrayType(elem_ty, 2**index_ty.width)
					else:
						assert False

			elif tokens[1] == "input":
				if p == 0:
					inputs.append((i, sorts[int(tokens[2])], tokens[3] if len(tokens) >= 4 else None))

			elif tokens[1] == "state":
				if p == 0:
					state_index[i] = len(state)
					state.append(sorts[int(tokens[2])])
				else:
					index = state_index[i]
					assert isinstance(index, int), index
					nodes[i] = builder.load(builder.gep(state_ptr, [
						ir.Constant(ir.IntType(32), 0),
						ir.Constant(ir.IntType(32), index)
					]))

			elif p == 0:
				continue

			elif tokens[1] == "one":
				nodes[i] = todo()
			elif tokens[1] == "ones":
				nodes[i] = todo()
			elif tokens[1] == "zero":
				nodes[i] = todo()
			elif tokens[1] == "const":
				assert not tokens[3].startswith("-")
				nodes[i] = ir.Constant(sorts[int(tokens[2])], int(tokens[3], 2))
			elif tokens[1] == "constd":
				nodes[i] = ir.Constant(sorts[int(tokens[2])], int(tokens[3], 10))
			elif tokens[1] == "consth":
				assert not tokens[3].startswith("-")
				nodes[i] = ir.Constant(sorts[int(tokens[2])], int(tokens[3], 16))
			elif tokens[1] == "init":
				todo()
			elif tokens[1] == "next":
				index = state_index[int(tokens[3])]
				value = nodes[int(tokens[4])]
				assert isinstance(index, int), index
				builder.store(value, builder.gep(state_next_ptr, [
					ir.Constant(ir.IntType(32), 0),
					ir.Constant(ir.IntType(32), index)
				]))
			elif tokens[1] == "bad":
				todo()
			elif tokens[1] == "constraint":
				todo()
			elif tokens[1] == "fair":
				todo()
			elif tokens[1] == "output":
				todo()
			elif tokens[1] == "justice":
				todo()
			else:
				if tokens[-1][0] not in "0123456789":
					name = tokens[-1]
					del tokens[-1:]
				else:
					name = ""
				op = getattr(bbuilder, "op_"+tokens[1], None)
				assert op, tokens[1]
				args = [int(arg) for arg in tokens[3:]]

				if tokens[1] in ("sext", "uext", "slice"):
					args = [nodes[args[0]]] + args[1:]
				else:
					args = [nodes[arg] for arg in args]

				retty = sorts[int(tokens[2])]
				#print("   ", [arg and hasattr(arg, "type") and arg.type for arg in args], "->", retty)
				if None in args:
					n = nodes[i] = ir.Constant(retty, ir.Undefined)
				else:
					n = nodes[i] = op(args, name)

				if n is None:
					todoops.add(tokens[1])

		if p == 1:
			builder.ret_void()

	for op in todoops:
		print(op)

with open("test.btor2") as f:
	module = ir.Module(name="test")

	# LIES
	module.data_layout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
	module.triple = "x86_64-pc-linux-gnu"

	parse(f.read(), module, "test")
	m = str(module)
	print(m)
	with open("test.ll", "w") as f:
		f.write(m)

	import os
	os.system("llc -O3 -o test.o -filetype=obj test.ll")
