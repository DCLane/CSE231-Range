
#include "../framework/lattice_design.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/ADT/SmallVector.h"

#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instruction.h"

#include "llvm/Pass.h"
#include "llvm/Support/InstIterator.h"

#include <limits>
#include <set> 
using namespace llvm;

#ifndef RANGE
#define RANGE 

// mem2reg pass should happen before this pass so no phi nodes and limited
// variable stored in memory

namespace range {

    typedef std::pair<llvm::ConstantInt *, llvm::ConstantInt *> Range;
    typedef std::pair<llvm::StringRef, Range> VarRange;
    typedef dataflow::LatticeElement<VarRange> VarRangeElement;

    class RangeLatticeElement : public VarRangeElement {
    public:
        RangeLatticeElement(dataflow::LatticeElementType t) {
            type = t;
        };

        RangeLatticeElement() {
            type = dataflow::REGULAR;
        };

        virtual RangeLatticeElement dumb_copy() {
            RangeLatticeElement e2;

            e2.type = type;
            e2.set = set;

            return e2;
        }



      virtual std::string llvm_print_set() {
            std::stringstream ss;
            switch(type) {
            case dataflow::REGULAR:
		outs() << "\tREGULAR\n";
                if(set.empty()) {
                    outs() << "\t  Set: empty";
                    break;
                }
		
		outs() << "\t  Set: \n"; 
                for(std::set<VarRange>::iterator it=set.begin(); it!=set.end(); ++it) {
                    if(it != set.begin()) {
                        ss << " | ";
                    }
                    VarRange p = *it;
                    outs() << "\t  " << std::string(p.first) << " : [" << p.second.first->getZExtValue() << ", " 
		    << p.second.second->getZExtValue () << "]\n";
                }
                break;
            case dataflow::BOTTOM:
                outs() << "\tBOTTOM\n";
                break;
            case dataflow::TOP:
                outs() << "\tTOP\n";
                break;
            }
            return ss.str();
      }


      virtual std::string print_set() {
            std::stringstream ss;
            switch(type) {
            case dataflow::REGULAR:
                if(set.empty()) {
                    ss << "empty";
                    break;
                }
                for(std::set<VarRange>::iterator it=set.begin(); it!=set.end(); ++it) {
                    if(it != set.begin()) {
                        ss << " | ";
                    }
                    VarRange p = *it;
                    ss << std::string(p.first) << " : [" << p.second.first->getZExtValue() << ", " 
		    << p.second.second->getZExtValue () << "]\n";
                }
                break;
            case dataflow::BOTTOM:
                ss << "BOTTOM";
                break;
            case dataflow::TOP:
                ss << "TOP";
                break;
            }
            return ss.str();
      }


	VarRange * find(llvm::StringRef s) {
            bool found_one = false;

            std::pair<llvm::StringRef, Range> * found = NULL;

            for (std::set<VarRange>::iterator i = set.begin(); i != set.end(); ++i)
            {
		llvm::outs() << "Inside find, searching for match of: " << (*i).first;
                if ((*i).first == s && found_one == false)
                {
                    found_one = true;
		    found = const_cast<VarRange *>(&(*i));
                }

                if ((*i).first == s && found_one == true)
                {
                    found = NULL;
                }
            }

            return found;
        }


        using VarRangeElement::e_union;
        virtual RangeLatticeElement e_union(RangeLatticeElement e) {

	    RangeLatticeElement new_element;

	    // union with top returns top (full set)
	    if (e.type == dataflow::TOP || type == dataflow::TOP)
	    {
		new_element.type = dataflow::TOP;
	    }

	    else if (e.type == dataflow::BOTTOM) {
		if (type == dataflow::BOTTOM) {
		    new_element.type = dataflow::BOTTOM;
		    new_element.set.clear();
		
		} else {
		    new_element.type = dataflow::REGULAR;
		    new_element.set  = set;
		}
	    }
	    
	    else if (type == dataflow::BOTTOM) {
		new_element.type = dataflow::REGULAR;
		new_element.set  = e.set;
	    }
		

	    // otherwise merge the two VarRangeElements (from this & e)
	    else {

		// Step through e's list looking for matching variables in this' set 
		for (std::set<VarRange>::iterator it = e.set.begin(); it != e.set.end(); ++it){
		    new_element.type = dataflow::REGULAR;
		    VarRange * var = find( (*it).first );
		    if (var == NULL) 
		    {
			new_element.set.insert(*it);
		    }
		    else
		    {
			// if there are matching variables, create the largest range
			llvm::ConstantInt *lower_a = (*it).second.first;	
			llvm::ConstantInt *upper_a = (*it).second.second;
			llvm::ConstantInt *lower_b = (*var).second.first;
			llvm::ConstantInt *upper_b = (*var).second.second;

			//std::pair<llvm::ConstantInt, llvm::ConstantInt> new_range;
			Range new_range;
			(lower_a < lower_b) ? new_range.first = lower_a  : new_range.first  = lower_b;
			(upper_a > upper_b) ? new_range.second = upper_a : new_range.second = upper_b;
			
			new_element.set.insert(VarRange( (*it).first, new_range ));
		    }
		}

		// Step through this' list for entries that didn't match with e's set
		for (std::set<VarRange>::iterator i = set.begin(); i != set.end(); ++i) {

		    llvm::outs() << "  Iteration of untion.\n";
		    if ( find( (*i).first ) == NULL )
		    {
			new_element.set.insert(*i);
		    } 
		}
	    }
	    
            return new_element;    
        };


        using VarRangeElement::intersect;
        virtual RangeLatticeElement intersect(RangeLatticeElement e) {

            RangeLatticeElement new_element;

	    // Any intersect with BOTTOM (empty set) returns BOTTOM            
            if (e.type == dataflow::BOTTOM || type == dataflow::BOTTOM)
            {
                new_element.type = dataflow::BOTTOM;
		new_element.set.clear();
            }

	    // Any intersect with TOP (full set) returns the other set
            else if (e.type == dataflow::TOP) {
		if (type == dataflow::TOP) {
		    new_element.type = dataflow::TOP;
		
		} else {
		    new_element.type = dataflow::REGULAR;
		    new_element.set  = set;
		}
	    }	
	
	    else if (type == dataflow::TOP) {
		new_element.type = dataflow::REGULAR;
		new_element.set  = e.set;
	    }
		
	    // If no TOP or BOTTOM entries
            else 
            {
		// Step through e's set looking for matches in this' set
		new_element.type = dataflow::REGULAR;
                for (std::set<VarRange>::iterator i = e.set.begin(); i != e.set.end(); ++i)
                {
		    VarRange * var = find( (*i).first );
		    if (var != NULL) 
		    {
			llvm::ConstantInt *lower_a = (*i).second.first;
			llvm::ConstantInt *upper_a = (*i).second.second;
			llvm::ConstantInt *lower_b = (*var).second.first;
			llvm::ConstantInt *upper_b = (*var).second.second;

			// compute the overlapping range
			Range new_range;
			(lower_a < lower_b) ? new_range.first  = lower_b : new_range.first  = lower_a;
			(upper_a < upper_b) ? new_range.second = upper_a : new_range.second = upper_b;			

			new_element.set.insert(VarRange( (*i).first, new_range ));
		    }
                }
            }

            return new_element;   
        };


	// What to do with Full set minus a REGULAR lattice type???
        using VarRangeElement::difference;
        virtual RangeLatticeElement difference(RangeLatticeElement e) {

	    RangeLatticeElement new_element;

	    // if you start w/ bottom or subtract top from anything
	    if (e.type == dataflow::TOP || type == dataflow::BOTTOM) {
		new_element.type = dataflow::BOTTOM;
		new_element.set.clear();
	    }

	    // Anything minus empty set is the original set
	    else if (e.type == dataflow::BOTTOM)
	    {
		new_element.set  = set;
		new_element.type = type;
	    }

	    // Otherwise - original set minus e's set
	    else
	    {
		new_element.type = dataflow::REGULAR;
		new_element.set = set;
		for (std::set<VarRange>::iterator i = e.set.begin(); i != e.set.end(); ++i)
		{
		    new_element.set.erase(*i);
		}
	    }

            return new_element;
        };


        virtual void insert(VarRange p) {
            set.insert(p);
        }
    };



    typedef dataflow::Lattice<RangeLatticeElement> TRangeLattice;
    class RangeLattice : public TRangeLattice {
        virtual RangeLatticeElement getTop() {
            return RangeLatticeElement(dataflow::TOP);
        };

        virtual RangeLatticeElement getBottom() {
            return RangeLatticeElement(dataflow::BOTTOM);
        };

        virtual RangeLatticeElement join(RangeLatticeElement e1, RangeLatticeElement e2) {
            return e1.intersect(e2);
        };

        virtual RangeLatticeElement meet(RangeLatticeElement e1, RangeLatticeElement e2) {
            return e1.e_union(e2);
        };
    };


    typedef dataflow::FlowFunctions<RangeLatticeElement> TRangeFlowFunction;
    class RangeFlowFunctions : public TRangeFlowFunction {
    public:

        //--- Methods ---
        virtual RangeLatticeElement apply(llvm::Instruction * inst, RangeLatticeElement element)
        {

	    if (llvm::dyn_cast<llvm::PHINode>(inst)) {
		return element;
	    }


            SmallVector<Constant*, 8> Ops;
            for (User::op_iterator i = inst->op_begin(), e = inst->op_end(); i != e; ++i) {
                Constant *Op = dyn_cast<Constant>(*i);
                Value *baseValue = dyn_cast<Value>(*i);
                ConstantExpr *NewCE = dyn_cast_or_null<ConstantExpr>(Op);
                if (!Op || NewCE) {
                    if (baseValue && baseValue->hasName())
                    {
                        VarRange *p = element.find(baseValue->getName());
                        if (p)
                        {
                            Ops.push_back(Op);	// Ops.push_back(p->second);
                            continue;
                        }
                    }
                    return element;  // All operands not constant!
                }

                Ops.push_back(Op);
            }


	    if (dyn_cast<CmpInst>(inst)){
		outs() << "Cmp ops: " << inst->getOperand(0) << ", " << inst->getOperand(1) << "\n";

	 	if (dyn_cast<ConstantInt>(inst->getOperand(0)) && dyn_cast<ConstantInt>(inst->getOperand(1))) {
		    Constant *a = Ops[0];
		    Constant *b = Ops[1];

		    //need to create a +inf and -inf ConstantInt for comparisons	
		    //outs() << "get type: " << inst->getOperand(0)->getType() << "\n";
//		    Value *max = ConstantInt(inst->getOperand(0)->getType(), 0xEFFFFFFFFFFFFFFF);
//		    Value *min = ConstantInt(inst->getOperand(0)->getType(), 0xFFFFFFFFFFFFFFFF);
//		    Range r = Range(*b, dyn_cast<ConstantInt>(min));
	
		    outs() << "a: " << *a << ", b: " << *b << "\n";
		}
	    }


            if (Instruction::isBinaryOp(inst->getOpcode())) {
		outs() << "Binary Op\n";
                RangeLatticeElement new_element = element.dumb_copy();
                Constant * c = ConstantExpr::get(inst->getOpcode(), Ops[0], Ops[1]);
                ConstantInt * ci = dyn_cast<llvm::ConstantInt>(c);

                if (!c || !ci)
                    return element;

                new_element.insert(VarRange(inst->getName(), Range(ci, ci)));
		new_element.type = dataflow::REGULAR;

                return new_element;
            }


/*
 	    if (Instruction::isBinaryOp(inst->getOpcode())) {
                RangeLatticeElement new_element = element.dumb_copy();
                inst_tuple c = inst_tuple(inst->getOpcode(), inst_pair(Ops[0], Ops[1]));

                if (element.find(c))
                {
                    return element;
                }

                new_element.insert(InstOpsPair(c, inst));
                return new_element;
            }
	    return element;
*/

	    return element;
        };

        virtual RangeLatticeElement merge(RangeLatticeElement a, RangeLatticeElement b) {
            return a.e_union(b);
        }

        virtual std::pair<RangeLatticeElement, RangeLatticeElement> branch(llvm::BranchInst* inst, RangeLatticeElement elem) {
            return std::make_pair<RangeLatticeElement, RangeLatticeElement>(elem, elem);
        }
    };
}

#endif
