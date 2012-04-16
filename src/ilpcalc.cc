#include "dr_api.h"
#include <map>
#include <vector>
#include <algorithm>
#include <stdint.h>
#include <stddef.h>

using namespace std;

struct BBInfo
{
    float m_fAvg;
    int m_iCount;
};

static uint numinst;
static std::vector<BBInfo*> vecBBInfo;

static void event_exit(void);
static dr_emit_flags_t event_basic_block(void *drcontext, void *tag, instrlist_t *bb, 
					 bool for_trace, bool translating);

static inline void IncInst(int num)
{
    numinst += num;
}

DR_EXPORT void dr_init(client_id_t id)
{
    dr_register_exit_event(event_exit);
    dr_register_bb_event(event_basic_block);

    //dr_fprintf(STDERR, "dr_init END\n");
}

static void event_exit(void)
{
    float avg = 0;
    double num = 0;
    double den = 0;
    for (std::vector<BBInfo*>::iterator iter = vecBBInfo.begin();
	 iter != vecBBInfo.end(); ++iter)
    {
	BBInfo *info = *iter;
	den += info->m_iCount;
    }

    for (std::vector<BBInfo*>::iterator iter = vecBBInfo.begin();
	 iter != vecBBInfo.end(); ++iter)
    {
	BBInfo *info = *iter;
	num = info->m_fAvg * info->m_iCount;	
	dr_global_free(info, sizeof(BBInfo));

	if (isnan(num))
	{
	    dr_fprintf(STDERR, "ERROR: The basic block is not included in the calculation since it results in a NAN; average = %f, num execution = %d\n", info->m_fAvg, info->m_iCount);
	    continue;
	}

	avg += (num / den);
    }

    vecBBInfo.clear();

    avg += num / den;

    dr_fprintf(STDERR, "The average number of instructions executed / cycle = %f\n", avg);
}

static inline void UpdateInstrCycle(std::vector<int>& eflagsCycles, instr_t *instr, bool bWrite, 
				    int& instrCycle)
{
    uint eflags = instr_get_eflags(instr);
    uint constants[7] = { EFLAGS_WRITE_CF, EFLAGS_WRITE_PF, EFLAGS_WRITE_AF, EFLAGS_WRITE_ZF,
			  EFLAGS_WRITE_SF, EFLAGS_WRITE_DF, EFLAGS_WRITE_OF };
    for (int i = 0; i < 7; i++)
    {
	if (!bWrite)
	    constants[i] = EFLAGS_WRITE_TO_READ(constants[i]);
	if ((eflags & constants[i]) != 0)
	{
	    instrCycle = max(instrCycle, eflagsCycles[i]);
	}
    }
}

static inline void UpdateInstrCycle(std::map<int, int>& regCycles, std::map<uint32_t, int>& memCycles,
				    opnd_t& opnd, int& instrCycle)
{
    if (opnd_is_memory_reference(opnd))
    {
	uint32_t addr = (uint32_t) opnd_get_addr(opnd);
	std::map<uint32_t, int>::iterator iter = memCycles.find(addr);
	if (iter == memCycles.end())
	{
	    memCycles.insert(std::make_pair<uint32_t, int>(addr, 0));
	    iter = memCycles.find(addr);
	}

	instrCycle = max(instrCycle, iter->second);
    }
    else
    if (opnd_is_reg(opnd))
    {
	int regid = (int) opnd_get_reg(opnd);
	std::map<int, int>::iterator iter = regCycles.find(regid);
	if (iter == regCycles.end())
	{
	    regCycles.insert(std::make_pair<int, int>(regid, 0));
	    iter = regCycles.find(regid);
	}
	
	instrCycle = max(instrCycle, iter->second);
    }

    return;
}

static inline void insert_counter_update(void *drcontext, instrlist_t *bb, instr_t *where, 
					 BBInfo* info, int offset)
{
    dr_save_arith_flags(drcontext, bb, where, SPILL_SLOT_1);

    instrlist_meta_preinsert(bb, where, 
			     LOCK(INSTR_CREATE_inc
				  (drcontext, OPND_CREATE_ABSMEM(((byte *) info) + offset, OPSZ_4))));

    /* restore flags */
    dr_restore_arith_flags(drcontext, bb, where, SPILL_SLOT_1);
}

static dr_emit_flags_t event_basic_block(void *drcontext, void *tag, instrlist_t *bb,
					 bool for_trace, bool translating)
{
    if (translating)
	return DR_EMIT_DEFAULT;

    instr_t *inst = NULL;
    int numCycles = 0, numInst = 0;
    std::map<int, int> regCycles;
    std::map<uint32_t, int> memCycles;
    std::vector<int> eflagsCycles(32, 0);
    int numSrc = 0, numDst = 0;
    
    for (inst = instrlist_first(bb); inst != NULL; inst = instr_get_next(inst))
    {
	// Indicates which cycle the instruction can start in
	int instrCycle = 0;
	numSrc = instr_num_srcs(inst);
	numDst = instr_num_dsts(inst);
	
	numInst++;
	
	int opcode = instr_get_opcode(inst);
	for (int j = 0; j < numSrc; j++)
	{
	    opnd_t opnd = instr_get_src(inst, j);
	    UpdateInstrCycle(regCycles, memCycles, opnd, instrCycle);
	}

	for (int j = 0; j < numDst; j++)
	{
	    opnd_t opnd = instr_get_dst(inst, j);
	    UpdateInstrCycle(regCycles, memCycles, opnd, instrCycle);
	}

	UpdateInstrCycle(eflagsCycles, inst, false, instrCycle);
	UpdateInstrCycle(eflagsCycles, inst, true, instrCycle);
	
	// Update the destination cycles to ensure that the next instruction cannot
	// start till the updated min cycle
	for (int j = 0; j < numDst; j++)
	{
	    opnd_t opnd = instr_get_dst(inst, j);
	    if (opnd_is_memory_reference(opnd))
	    {
		uint32_t addr = (uint32_t) opnd_get_addr(opnd);
		// The address can be only be used after the instruction has finished (1 cycle)
		memCycles[addr] = instrCycle + 1;
	    }
	    else if (opnd_is_reg(opnd))
	    {
		int regid = (int) opnd_get_reg(opnd);
		regCycles[regid] = instrCycle + 1;
	    }
	}

	// Update the EFLAGS cycles
	int eflags = instr_get_eflags(inst);
	uint constants[7] = { EFLAGS_WRITE_CF, EFLAGS_WRITE_PF, EFLAGS_WRITE_AF, EFLAGS_WRITE_ZF,
			      EFLAGS_WRITE_SF, EFLAGS_WRITE_DF, EFLAGS_WRITE_OF};
    
	for (int i = 0; i < 7; i++)
	{
	    if ((eflags & constants[i]) != 0)
	    {
		eflagsCycles[i] = instrCycle + 1;
	    }
	}

	instrCycle++;
	numCycles = max(instrCycle, numCycles);
    }

    if (numInst == 0 || numCycles == 0)
	return DR_EMIT_DEFAULT;

    float avg = (float) numInst / (float) numCycles;
    if (isnan(avg))
    {
	dr_fprintf(STDERR, "ERROR NAN: The average calculated in the basic block will not be used; num instructions = %d, num cycles required = %d\n", numInst, numCycles);
	return DR_EMIT_DEFAULT;
    }

    BBInfo *info = (BBInfo *) dr_global_alloc(sizeof(BBInfo));
    info->m_fAvg = avg;
    info->m_iCount = 1;

    vecBBInfo.push_back(info);
 
    //dr_fprintf(STDERR, "numCycles = %d, numInst = %d, avg = %f\n", numCycles, numInst, avg);

    // Insert instruction to track the number of times this basic block is executed
    insert_counter_update(drcontext, bb, inst,
			  info, offsetof(BBInfo, m_iCount));

    return DR_EMIT_DEFAULT;
}
