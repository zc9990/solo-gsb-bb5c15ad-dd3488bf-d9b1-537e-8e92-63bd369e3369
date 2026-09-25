'use strict';

/**
 * 连场轮换排班（整场联合求解）。
 *
 * 规则（以全量重放结果为准）：
 *  - 仅「整组生效」的提示纳入排班；失败提示不计轮次，也不参与相邻约束
 *    （中间隔着失败提示的两条生效提示仍算相邻）；
 *  - 组内每条道具转移 = 一个岗位，仍须由具备该道具搬运资格的人员承担，
 *    且同一人员在同一组内最多承担一个岗位（与逐提示岗位表一致）；
 *  - 同一人员不得出现在相邻两条生效提示中；
 *  - 对整场联合求解：为让后续提示有解，允许回溯调整前序提示的合法分配，
 *    而不是逐组贪心定死后不再更改；
 *  - 无法全覆盖时：报告「首个无法形成可行前缀的提示」及其前一条生效提示，
 *    不输出部分岗位表。
 *
 * 求解方法：按生效提示序列做带回溯的深度优先搜索，状态为
 * （第 i 条生效提示，上一条生效提示的用人集合）；无解状态记忆化，避免重复展开。
 * 搜索中记录已到达的最长可行前缀，整场无解时据此定位首个无法覆盖的提示：
 * 若最长可行前缀为 L 条，则第 L 条（0 起）生效提示即首个无法形成可行前缀的提示。
 *
 * 人员、资格或提示变化后，由服务端用最新数据整体重算（本模块为纯函数）。
 */

/**
 * 生成连场轮换排班表。
 *
 * @param {Array<{number:number, note:string, transfers:Array}>} cues 已按提示号升序
 * @param {Array<{number:number, ok:boolean}>} results 全量重放结果（replay().results）
 * @param {Array<{name:string, props:string[]}>} staff 人员及其可搬运道具名单
 * @returns {{status:'ok'|'infeasible'|'empty', effectiveCount:number, skippedCount:number,
 *   rounds:Array<{number:number, note:string,
 *     positions:Array<{prop:string, from:string, to:string, staff:string}>}>,
 *   failure:null|{number:number, note:string, transferCount:number,
 *     feasiblePrefixCount:number, previousNumber:number|null, previousNote:string|null}>}}
 *   - ok：整场可排，rounds 为逐轮完整岗位表（轮次 = 生效提示序号，失败提示不计）；
 *   - infeasible：无法全覆盖，rounds 恒为空（不输出部分岗位表），failure 给出首个
 *     无法形成可行前缀的提示号及其前一条生效提示号（无前一条时为 null）；
 *   - empty：没有生效提示，无需排班。
 */
function computeRotation(cues, results, staff) {
  const resultByNumber = new Map(results.map((r) => [r.number, r]));

  // 仅纳入全量重放生效的提示，保持提示号升序；失败提示不计轮次
  const effective = cues.filter((c) => {
    const r = resultByNumber.get(c.number);
    return r && r.ok;
  });
  const skippedCount = cues.length - effective.length;

  const staffNames = staff.map((s) => s.name);
  const qualified = staff.map((s) => new Set(s.props));

  // 每条转移的合格人员（人员序号，按人员录入顺序）
  const candIdx = effective.map((cue) =>
    cue.transfers.map((t) => {
      const list = [];
      for (let j = 0; j < staff.length; j++) {
        if (qualified[j].has(t.prop)) list.push(j);
      }
      return list;
    })
  );

  const n = effective.length;
  if (n === 0) {
    return { status: 'empty', effectiveCount: 0, skippedCount, rounds: [], failure: null };
  }

  const memo = new Set(); // 已知无解的状态：'i|已排序人员序号,…'
  let maxPrefix = 0; // 已探明可行的前缀长度（生效提示条数）

  /**
   * 从第 i 条生效提示继续排班；prev 为上一条生效提示的用人集合（人员序号）。
   * 成功返回从第 i 条开始的完整分配（每条提示 = 与 transfers 对齐的人员序号数组），
   * 无解返回 null。
   */
  function dfs(i, prev, prevKey) {
    if (i === n) return [];
    if (i > maxPrefix) maxPrefix = i; // 进入此状态即说明前 i 条已有合法分配
    const key = `${i}|${prevKey}`;
    if (memo.has(key)) return null;

    const cands = candIdx[i];
    const assign = new Array(cands.length).fill(-1);
    const usedHere = new Set(); // 本组已占用人员（同组互不相同）

    // 按转移录入顺序逐条挑人；凑齐一种整组合法分配就递归下一条生效提示
    function place(t) {
      if (t === cands.length) {
        const nextKey = [...usedHere].sort((a, b) => a - b).join(',');
        return dfs(i + 1, usedHere, nextKey);
      }
      for (const j of cands[t]) {
        if (prev.has(j) || usedHere.has(j)) continue; // 相邻轮次不得同人；同组不得同人
        usedHere.add(j);
        assign[t] = j;
        const rest = place(t + 1);
        if (rest) return rest;
        usedHere.delete(j);
        assign[t] = -1;
      }
      return null;
    }

    const rest = place(0);
    if (!rest) {
      memo.add(key);
      return null;
    }
    // 此刻 assign 已填满本组分配，只在本层 prepend 一次
    return [assign.slice(), ...rest];
  }

  const solution = dfs(0, new Set(), '');

  if (solution) {
    return {
      status: 'ok',
      effectiveCount: n,
      skippedCount,
      rounds: effective.map((cue, i) => ({
        number: cue.number,
        note: cue.note,
        positions: cue.transfers.map((t, ti) => ({
          prop: t.prop,
          from: t.from,
          to: t.to,
          staff: staffNames[solution[i][ti]],
        })),
      })),
      failure: null,
    };
  }

  // 整场无解：maxPrefix 为最长可行前缀（条数），第 maxPrefix 条（0 起）即首个无法覆盖的提示
  const first = effective[maxPrefix];
  const prevCue = maxPrefix > 0 ? effective[maxPrefix - 1] : null;
  return {
    status: 'infeasible',
    effectiveCount: n,
    skippedCount,
    rounds: [], // 不输出部分岗位表
    failure: {
      number: first.number,
      note: first.note,
      transferCount: first.transfers.length,
      feasiblePrefixCount: maxPrefix, // 此前有多少条生效提示本可排开（仍不输出其岗位表）
      previousNumber: prevCue ? prevCue.number : null,
      previousNote: prevCue ? prevCue.note : null,
    },
  };
}

module.exports = { computeRotation };
