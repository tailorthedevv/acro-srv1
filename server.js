const { pack, unpack } = require("msgpackr") // leave this
const WebSocket = require("ws"), { WebSocketServer } = WebSocket
const { performance } = require('perf_hooks')
const { sha256 } = require('js-sha256')
const sqlite3 = require('sqlite3').verbose()
const axios = require('axios');

// adding a comment to activate autodeploy (maybe) [can be removed later]

class Quadtree {
  constructor(mapsize, x = 0, y = 0, objects = {}) {
    this.size = mapsize;
    this.objects = objects;
    this.centerX = x;
    this.centerY = y;
  };
  insert(id, object, type) {
    if (!this.objects[id]) this.objects[id] = { type: type, obj: object };
  };
  remove(id) {
    delete this.objects[id];
  };
  updateSize(mapsize) {
    this.size = mapsize;
  };
  updateObject(id, object) {
    if (this.objects[id]) this.objects[id].obj = object;
  };
  getQuadrant(id) {
    const obj = this.objects[id]?.obj;
    if (!obj) return '-1';
    /*
    Quadrants:
    Top Right - 0
    Bottom Right - 1
    Bottom Left - 2
    Top Left - 3
    Invalid - (-1)
    */
    const size = this.size;
    let quadrant = [];
    let sector = -1;
    if (obj.x + this.centerX >= size / 2 && obj.y + this.centerY >= size / 2) {
      quadrant.push('0');
      sector = 0;
    };
    if (obj.x + this.centerX >= size / 2 && obj.y + this.centerY < size / 2) {
      quadrant.push('1');
      sector = 1;
    };
    if (obj.x + this.centerX < size / 2 && obj.y + this.centerY < size / 2) {
      quadrant.push('2');
      sector = 2;
    };
    if (obj.x + this.centerX < size / 2 && obj.y + this.centerY >= size / 2) {
      quadrant.push('3');
      sector = 3;
    };
    return quadrant.join('-');
  };
  getNearObjects(id, searchType) {
    const obj = this.objects[id]?.obj;
    if (!obj) return [];
    let output = [];
    for (let oid in this.objects) {
      if (oid == id) continue;
      if (this.objects[oid].type !== searchType) continue;
      if (this.getQuadrant(oid) != this.getQuadrant(id)) continue;
      output.push(this.objects[oid]);
    };
    return output;
  };
};

const hrtime = process.hrtime();
const startTime = Math.round((hrtime[0] * 1000) + (hrtime[1] / 1000000));
const performanceNow = function() {
  const hrtime = process.hrtime();
  return Math.round((hrtime[0] * 1000) + (hrtime[1] / 1000000)) - startTime;
};
function getXPToNextLevel(level) {
  return level <= 0 ? 0 : 100 * 1.2 ** (level - 1);
};

const badWords = ['nigger', 'niggah', 'nigga', 'faggot', 'tranny', 'cunt', 'nazi', 'sigma', 'skibidi', 'ohio', 'fanum'];

const letterConversions = [{
  original: 'a',
  converted: 'а@4'
}, {
  original: 'e',
  converted: 'е3'
}, {
  original: 'x',
  converted: 'х'
}, {
  original: 'j',
  converted: 'ј'
}, {
  original: 'k',
  converted: 'к'
}, {
  original: 'm',
  converted: 'м'
}, {
  original: 'h',
  converted: 'н'
}, {
  original: 'o',
  converted: 'о0'
}, {
  original: 'p',
  converted: 'р'
}, {
  original: 'c',
  converted: 'с'
}, {
  original: 't',
  converted: 'т'
}, {
  original: 'y',
  converted: 'у'
}, {
  original: 'b',
  converted: 'в'
}, {
  original: 's',
  converted: 'ѕ\\$'
}, {
  original: 'w',
  converted: 'ш'
}, {
  original: 'i',
  converted: '1'
}, {
  original: 'z',
  converted: '2'
}, {
  original: 'g',
  converted: '96'
}, {
  original: 'n',
  converted: 'п'
}, {
  original: 'r',
  converted: 'г'
}];

const polygonStats = {
  3: {
    name: 'Triangle',
    color: 20,
  },
  4: {
    name: 'Square',
    color: 21,
  },
  5: {
    name: 'Pentagon',
    color: 22,
  },
  6: {
    name: 'Hexagon',
    color: 23,
  },
  7: {
    name: 'Heptagon',
    color: 24,
  },
  8: {
    name: 'Octagon',
    color: 25,
  },
  9: {
    name: 'Nonagon',
    color: 26,
  },
  10: {
    name: 'Decagon',
    color: 27,
  },
  11: {
    name: 'Hendecagon',
    color: 28,
  },
  12: {
    name: 'Dodecagon',
    color: 29,
  },
  13: {
    name: 'Tridecagon',
    color: 30,
  },
  14: {
    name: 'Tetradecagon',
    color: 5,
  },
  15: {
    name: 'Pentadecagon',
    color: 5,
  },
  16: {
    name: 'Hexadecagon',
    color: 5,
  },
  17: {
    name: 'Heptadecagon',
    color: 5,
  },
  18: {
    name: 'Octadecagon',
    color: 5,
  },
  19: {
    name: 'Enneadecagon',
    color: 5,
  },
  20: {
    name: 'Icosagon',
    color: 5,
  }
};

function inDistance(coords1, coords2, distance) {
  return ((coords2[0] - coords1[0]) ** 2 + (coords2[1] - coords1[1]) ** 2) <= distance ** 2;
};

let bulletIDs = [];
const speedMult = 3;
const globalDamageMult = 7.5;

const mradToDeg = (mrad) => mrad * 180 / (1000 * Math.PI);
const radToDeg = (rad) => mradToDeg(rad * 1000);
const degToMrad = (deg) => deg * (1000 * Math.PI) / 180;
const degToRad = (deg) => degToMrad(deg) / 1000;
const radToMrad = (rad) => rad * 1000;
const mradToRad = (mrad) => mrad / 1000;

function encryptIP(ip) {
  const moddedIP = (parseInt(ip.split('.')[0]) + 15) + '.' + ip.split('.').slice(1).join('.');
  return sha256(sha256(moddedIP) + sha256('Goodluck figuring out how the heck this is supposed to be decrypted :skull:'));
};

function limit(tank) {
  const limits = {
      sides: 50,
  };
  let limited = JSON.parse(JSON.stringify(tank));
  if (limited.layers) for (let i in limited.layers) {
      let layer = limited.layers[i];
      if (layer && Math.abs(layer.sides) > limits.sides) {
          if (layer.sides < 0) {
              limited.layers[i].sides = -limits.sides;
          } else {
              limited.layers[i].sides = limits.sides;
          };
      };
  };
  function limitAura(aura) {
      if (aura && Math.abs(aura.sides) > limits.sides) {
          if (aura.sides < 0) {
              aura.sides = -limits.sides;
          } else {
              aura.sides = limits.sides;
          };
      };
  };
  if (limited.auras) for (let i in limited.auras) {
      limitAura(limited.auras[i]);
  };
  if (limited.gadgets) for (let i in limited.gadgets) {
      let gadget = limited.gadgets[i];
      if (gadget) {
          if (gadget.type === 3) {
              limited.gadgets[i].tank = limit(gadget.tank);
          } else if (gadget.type === 2) {
              limitAura(limited.gadgets[i]);
          };
      };
  };
  return limited;
};

let dims = [{
  id: 'main',
  mapsize: 6000,
  gamemode: 0,
  shapemult: 1,
  gridsize: 30,
  bgcolor: '#CDCDCD',
  gridcolor: '#C8C8C8',
  ip: null,
  quadtree: new Quadtree(6000)
}];

const ASPB = [];

const commands = [];
class Command {};
Command.add = (syntax, permissions, func) => {
  syntax.replace(/\([^ )]+\)\s*/g, m => {
    let newname = m.trim().slice(1).slice(0, -1);
    commands.push({
      s: syntax.replace(/^\/[^ ]+/, '/' + newname).replace(/\([^ )]+\)\s*/g, '').trim(),
      f: func,
      n: '/' + newname,
      p: permissions,
      alias: syntax.split(' ')[0]
    });
    return '';
  });
  commands.push({
    s: syntax.replace(/\([^ )]+\)\s*/g, '').trim(),
    f: func,
    n: syntax.split(' ')[0],
    p: permissions
  });
};
Command.add('/help (?) <command?>', 'none', () => {}); // This will be hardcoded to work automatically.
Command.execute = (me, cmd, parameters) => {
  if (cmd == '/help' || cmd == '/?') {
    if (parameters.length >= 1) {
      let syntax;
      for (let i in commands) {
        if (commands[i].n === parameters[0] || commands[i].n.slice(1) === parameters[0]) {
          syntax = commands[i].s;
          break;
        };
      };
      if (syntax) {
        me.sendPacket([1, 'addNotification', `Syntax: ${syntax}`]);
      } else {
        me.sendPacket([1, 'addNotification', `Unknown command: ${parameters[0]}`]);
      };
    } else {
      let message = [];
      let aliases = {};
      for (let i in commands) {
        let allowed = true;
        let permHTML = '';
        switch (commands[i].p) {
          case 'none':
            break;
          case 'yt':
            if (!me.yt) {
              allowed = false;
            }
            permHTML = '<strong style="color: red;">(YouTuber+)</strong>';
            break;
          case 'mod':
            if (!me.mod) {
              allowed = false;
            }
            permHTML = '<strong style="color: #349beb;">(Moderator+)</strong>';
            break;
          case 'admin':
            if (!me.admin) {
              allowed = false;
            };
            permHTML = '<strong style="color: #eb7734;">(Admin+)</strong>';
            break;
          case 'dev':
            if (!me.developer) {
              allowed = false;
            }
            permHTML = '<strong style="color: #ae24c9;">(Developer)</strong>';
            break;
        };
        if (!allowed) continue;
        if (commands[i].alias) {
          if (aliases[commands[i].alias]) {
            aliases[commands[i].alias].push(commands[i].n);
          } else {
            aliases[commands[i].alias] = [commands[i].n];
          };
        } else {
          if (aliases[commands[i].n]) {
            let cmd = commands[i].s.split(' ');
            for (let j of aliases[commands[i].n]) {
              cmd.splice(1, 0, '(' + j + ')');
            };
            const toPush = `${permHTML} <strong>${cmd[0]}</strong> ${cmd.slice(1).join(' ').replace(/</g, '&lt;').replace(/>/g, '&gt;')}`.trim();
            message.push(toPush);
          } else {
            const toPush = `${permHTML} <strong>${commands[i].s.split(' ')[0]}</strong> ${commands[i].s.split(' ').slice(1).join(' ').replace(/</g, '&lt;').replace(/>/g, '&gt;')}`.trim();
            message.push(toPush);
          };
        };
      };
      me.sendPacket([12, 'popup', 'Commands', message.join('<br><br>')]);
    };
    return;
  };
  let c = {};
  for (let i in commands) {
    if (commands[i].n === cmd) {
      c = { ...commands[i] };
      break;
    };
  };
  if (JSON.stringify(c) === '{}') {
    me.sendPacket([1, 'addNotification', 'Invalid Command!']);
    return;
  };
  switch (c.p) {
    case 'none':
      break;
    case 'yt':
      if (!me.yt) {
        me.sendPacket([1, 'addNotification', 'You do not have permission to run that command.']);
        return;
      };
      break;
    case 'mod':
      if (!me.mod) {
        me.sendPacket([1, 'addNotification', 'You do not have permission to run that command.']);
        return;
      };
      break;
    case 'admin':
      if (!me.admin) {
        me.sendPacket([1, 'addNotification', 'You do not have permission to run that command.']);
        return;
      };
      break;
    case 'dev':
      if (!me.developer) {
        me.sendPacket([1, 'addNotification', 'You do not have permission to run that command.']);
        return;
      };
      break;
    default:
      me.sendPacket([1, 'addNotification', 'Ran into an error checking permissions.']);
      return;
  };
  c.s.split(' ').slice(1).join(' ');
  const params = c.s.split(' ');
  params.splice(0, 1);
  let optionals = [];
  let lastinf = false;
  for (let i in params) {
    if (params[i].slice(-2, -1) == '?') {
      optionals.push(params[i]);
    };
    if (params[i].slice(-2, -1) == '+') {
      lastinf = true;
    };
  };
  if (parameters.length >= params.length - optionals.length) {
    let targ;
    if (params.includes('<target>')) {
      targ = params.indexOf('<target>');
    };
    const toPass = [];
    for (let i in params) {
      if (params[i] != '<target>') {
        if (parameters.length - 1 >= i) {
          if (lastinf && i == params.length - 1) {
            toPass.push(parameters.slice(i).join(' '));
            break;
          } else {
            toPass.push(parameters[i]);
          };
        } else {
          toPass.push(undefined);
        };
      };
    };
    function getTarget(me, target) {
      if (target == 'me' || target == '@s' || target == 'myself') {
        return me;
      } else if (target == 'all' || target == 'everything' || target == '@e') {
        return 'all';
      } else if (target == 'everyone' || target == 'players' || target == '@a') {
        return 'players';
      } else if (target == 'global') {
        return clients[me].admin ? 'global' : me;
      } else if (target == 'shapes' || target == 'polygons' || target == '@p') {
        return 'shapes';
      } else {
        return target;
      };
    };
    try {
      if (targ !== undefined) {
        let passedTarg = getTarget(me.clientId, parameters[targ]);
        if (passedTarg == 'all') {
          for (let i in clients) {
            if (clients[i] && clients[i].tank && clients[i].dim == me.dim) c.f(me, i, ...toPass, clients[i]);
          };
          for (let i in shapes) {
            if (shapes[i] && shapes[i].dim == me.dim) c.f(me, i, ...toPass, shapes[i]);
          };
        } else if (passedTarg == 'players') {
          for (let i in clients) {
            if (clients[i] && clients[i].tank && clients[i].dim == me.dim) c.f(me, i, ...toPass, clients[i]);
          };
        } else if (passedTarg == 'shapes') {
          for (let i in shapes) {
            if (shapes[i] && shapes[i].dim == me.dim) c.f(me, i, ...toPass, shapes[i]);
          };
        } else if (passedTarg == 'global') {
          for (let i in clients) {
            if (clients[i] && clients[i].tank) c.f(me, i, ...toPass, clients[i]);
          };
          for (let i in shapes) {
            if (shapes[i]) c.f(me, i, ...toPass, shapes[i]);
          };
        } else {
          if (clients[passedTarg] && clients[passedTarg].tank && clients[passedTarg].dim == me.dim) c.f(me, passedTarg, ...toPass, clients[passedTarg]);
          else if (shapes[passedTarg] && shapes[passedTarg].dim == me.dim) c.f(me, passedTarg, ...toPass, shapes[passedTarg]);
        };
      } else {
        c.f(me, ...toPass, me);
      };
    } catch (e) {
      console.log(`Command execution error: ${e}.`);
    };
  } else {
    me.sendPacket([1, 'addNotification', `This command requires ${params.length - optionals.length} parameters!`]);
    me.sendPacket([1, 'addNotification', `Syntax: ${c.s}`]);
    return;
  };
};
// Please dont delete this class, I love using classes like this :)

Command.add('/kick <target> <reason+>', 'yt', (ws, target, reason, targetObj) => {
  if (clients[target]) {
    if (targetObj.developer && !ws.developer) {
      ws.sendPacket([1, 'addNotification', 'You can\'t kick a developer, silly!']);
      return;
    };
    targetObj.tank = 0;
    targetObj.sendPacket(['kickMessage', 'You were kicked by a moderator!', reason]);
  } else if (shapes[target]) {
    delete shapes[target];
  };
});

Command.add('/givedev', 'none', (ws) => {
  ws.sendPacket([12, 'popup', 'Developer Token:', 'https://acropolis.ac/?token=bG9uZ2FoaHRva2VuaGVoZXJpY2tyb2xsdG9rZW5yZWFsPz8/Pz95ZWFoaXRzcmVhbGJ0d2lmeW91ZGVjb2RlZHRoaXN0aGVudWhoaGRvbnRhc2txdWVzdGlvbnMsb2s/']);
});

Command.add('/aspb <name>', 'dev', (ws, name) => {
  ASPB.push(name);
  ws.sendPacket([1, 'addNotification', `Successfully ASPB'd ${name}.`]);
  for (let i in clients) {
    ASPB.forEach(name => {
      if (clients[i].tank.name.includes(name)) {
          clients[i].ban(`This is an ASPB (Automatic Serverside Purge Ban). If you feel this is a false ban, submit an appeal.`);
      };
    });
  };
});

Command.add('/cbullets (clearbullets)', 'none', (ws) => {
  bullets = bullets.filter((item, i) => {
    const condition = ws.dim != item.parentData.dim;
    if (!condition) {
      const dead = bullets[i];
      dead.dead = true;
      deadBullets.push(dead);
      let thisDim = {};
      for (let dim of dims) {
        if (dim.id === ws.dim) {
          thisDim = dim;
          break;
        };
      };
      thisDim.quadtree.remove('b' + item.id);
    };
    return condition;
  });
});

Command.add('/cshapes (clearshapes) (cpolygons) (clearpolygons)', 'none', (ws) => {
  for (let i in shapes) {
    if (shapes[i].dim == ws.dim) {
      const dead = shapes[i];
      dead.dead = true;
      deadShapes[i] = dead;
      let thisDim = {};
      for (let dim of dims) {
        if (dim.id === ws.dim) {
          thisDim = dim;
          break;
        };
      };
      thisDim.quadtree.remove(i);
      delete shapes[i];
    };
  };
});

Command.add('/popup <target> <title> <message+>', 'yt', (ws, target, title, message) => {
  clients[target].sendPacket([12, 'popup', title, message]);
});

Command.add('/bc <target> <message+>', 'yt', (ws, target, message) => {
  clients[target].sendPacket([1, 'addNotification', message]);
});

Command.add('/gpl <target>', 'dev', (ws, target) => {
  if (clients[target]) {
    if (clients[target].developer) ws.sendPacket([1, 'addNotification', `ID ${target}: Developer`]);
    else if (clients[target].admin) ws.sendPacket([1, 'addNotification', `ID ${target}: Admin`]);
    else if (clients[target].mod) ws.sendPacket([1, 'addNotification', `ID ${target}: Moderator`]);
    else if (clients[target].yt) ws.sendPacket([1, 'addNotification', `ID ${target}: YouTuber`]);
  };
});

Command.add('/ban <ip> <reason+>', 'mod', (ws, ip, reason) => {
  db.run('INSERT INTO banned_ips (ip) VALUES (?)', [ip], err => {
    if (err) {
      ws.sendPacket([1, 'addNotification', 'IP is already banned!']);
      return;
    };
    db.run('INSERT INTO ban_reasons (ip, reason) VALUES (?, ?)', [ip, reason], err => {
      if (err) {
        console.error(err);
        ws.sendPacket([1, 'addNotification', 'Failed to save ban reason.']);
      } else {
        ws.sendPacket([1, 'addNotification', 'IP banned successfully.']);
        for (let i in clients) {
          if (sha256(clients[i].ip) === ip || encryptIP(clients[i].ip) === ip) {
            clients[i].close();
            break;
          };
        };
      };
    });
  });
});

Command.add('/unban <ip>', 'admin', (ws, ip) => {
  db.run('DELETE FROM banned_ips WHERE ip = ?', [ip], function(err) {
    if (this.changes === 0) ws.sendPacket([1, 'addNotification', 'IP is not banned!']);
    else if (!err) ws.sendPacket([1, 'addNotification', 'IP unbanned successfully.']);
  });
  db.run('DELETE FROM ban_reasons WHERE ip = ?', [ip], err => {});
});

Command.add('/getip (gip) <target>', 'admin', (ws, target) => {
  if (clients[target].developer && !ws.developer) {
    ws.sendPacket([1, 'addNotification', 'You can\'t get the IP of a developer, silly!']);
    return;
  };
  const moddedIP = encryptIP(clients[target].ip);
  if (clients[target]) ws.sendPacket([1, 'addNotification', moddedIP]);
});

Command.add('/dstats (dimstats) (dimensionstatistics) (dims)', 'none', (ws) => {
  let stats = '';
  let privates = {
    count: 0,
    players: 0
  };
  for (let i in dims) {
    if (dims[i].private) {
        privates.count++;
        for (let j in clients) {
            if (clients[j] && clients[j].dim === dims[i].id) {
                privates.players++;
            };
        };
        continue;
    };
    let players = 0;
    for (let j in clients) {
      if (clients[j] && clients[j].dim === dims[i].id) {
        players++;
      };
    };
    stats += dims[i].id + ' - ' + players + ' players';
    stats += '<br>';
  };
  stats += `<br>Private Dimensions: ${privates.count} - ${privates.players} players`;
  ws.sendPacket([12, 'popup', 'Dimension Stats', stats]);
});

const ignoredDimNames = ['missing"101!.PRIV', '[Far▼Out]_[Lowly]_Strangers_(Main)'];  // List of dimension names to ignore from the regex check in /cdim (eh its just for mods who want their private place to hang out in)

Command.add('/bulletaccess (bulleta) (baccess) (ba) <target> <state?>', 'mod', (ws, target, state, targetObj) => {
  state ??= '1';
  targetObj.baccess = ['1', 'true'].includes(state);
});

Command.add('/cdim (ndim) (createdimension) (newdimension) <id> <mapsize?> <gamemode?> <shapemult?> <gridsize?> <bgcolor?> <gridcolor?>', 'none', (ws, id, mapsize, gamemode, shapemult, gridsize, bgcolor, gridcolor) => {
  dimsMade = 0;
  id = id.slice(0, 50);
  newid = id.replace(/</g, '&lt;').replace(/>/g, '&gt;');

  if (!ignoredDimNames.includes(id) && !/^[a-zA-Z0-9_-]+$/.test(id)) {
    ws.sendPacket([1, 'addNotification', 'Dimension name must contain only letters, numbers, underscores, or hyphens.']);
    return;
  }

  for (let i of dims) {
    if (i.id === newid) {
      ws.sendPacket([1, 'addNotification', 'This dimension already exists!']);
      return;
    };
    if (i.ip === ws.ip) {
      dimsMade += 1;
    };
  };
  if (dimsMade >= 3) {
    ws.sendPacket([1, 'addNotification', 'You cannot create more than 3 dimensions!']);
    return;
  };
  dims.push({
    id: newid,
    mapsize: parseInt(mapsize) || 6000,
    gamemode: gamemode,
    shapemult: isNaN(parseFloat(shapemult)) ? 1 : parseFloat(shapemult),
    gridsize: gridsize,
    bgcolor: bgcolor || '#CDCDCD',
    gridcolor: gridcolor || '#C8C8C8',
    ip: ws.ip,
    private: false,
    quadtree: new Quadtree(parseInt(mapsize) || 6000)
  });
  ws.sendPacket([1, 'addNotification', `Successfully created dimension "${id}".`]);
  console.log(`Dim Created: ${id}`);
});

Command.add('/pdim (privatedimension) <id> <mapsize?> <gamemode?> <shapemult?> <gridsize?> <bgcolor?> <gridcolor?>', 'none', (ws, id, mapsize, gamemode, shapemult, gridsize, bgcolor, gridcolor) => {
    dimsMade = 0;
    id = id.slice(0, 50);
    newid = id.replace(/</g, '&lt;').replace(/>/g, '&gt;');

    if (!ignoredDimNames.includes(id) && !/^[a-zA-Z0-9_-]+$/.test(id)) {
      ws.sendPacket([1, 'addNotification', 'Dimension name must contain only letters, numbers, underscores, or hyphens, unless it\'s a special name!']);
      return;
    }

    for (let i of dims) {
      if (i.id === newid) {
        ws.sendPacket([1, 'addNotification', 'This dimension already exists!']);
        return;
      };
      if (i.ip === ws.ip) {
        dimsMade += 1;
      };
    };
    if (dimsMade >= 3) {
      ws.sendPacket([1, 'addNotification', 'You cannot create more than 3 dimensions!']);
      return;
    };
    dims.push({
      id: newid,
      mapsize: parseInt(mapsize) || 6000,
      gamemode: gamemode,
      shapemult: isNaN(parseFloat(shapemult)) ? 1 : parseFloat(shapemult),
      gridsize: gridsize,
      bgcolor: bgcolor || '#CDCDCD',
      gridcolor: gridcolor || '#C8C8C8',
      ip: ws.ip,
      private: true,
      quadtree: new Quadtree(parseInt(mapsize) || 6000)
    });
    ws.sendPacket([1, 'addNotification', `Successfully created private dimension "${id}".`]);
    ws.dim = newid;
    ws.isNew = true;
    ws.inPrivate = true;
    ws.sendPacket(['removeExisting']);
    ws.sendPacket(['dimChange', 'gridSize', parseInt(gridsize) || 30]);
    ws.sendPacket(['dimChange', 'backgroundColor', bgcolor || '#CDCDCD']);
    ws.sendPacket(['dimChange', 'gridColor', gridcolor || '#C8C8C8']);
    console.log(`Private Dim Created: ${id}`);
});

Command.add('/dim <target> <dim>', 'none', (ws, target, dim, count) => {
  if (!clients[target]) return;
  newdim = dim.replace(/</g, '&lt;').replace(/>/g, '&gt;');
  if (!ws.mod && target != ws.clientId) {
    ws.sendPacket([1, 'addNotification', 'You must be a moderator or higher to /dim other players!']);
    return;
  };
  if (clients[target].dim == newdim) {
    clients[target].sendPacket([1, 'addNotification', `You are already in "${dim}" dimension!`]);
    return;
  };
  for (let i of dims) {
    if (newdim === i.id) {
      if (clients[target].inPrivate) {
        let count = -1;
        for (let j in clients) {
            if (clients[j].dim === clients[target].dim) {
                count++;
            };
        };
        if (count <= 0) {
            for (let j in dims) {
                if (dims[j].id === clients[target].dim) {
                    dims.splice(j, 1);
                    break;
                };
            };
        };
      };
      clients[target].inPrivate = i.private;
      clients[target].dim = newdim;
      clients[target].sendPacket([1, 'addNotification', `Set your dimension to "${newdim}"`]);
      clients[target].isNew = true;
      clients[target].bodyUpdate = true;
      clients[target].sendPacket(['removeExisting']);
      clients[target].weaponUpdate = true;
      clients[target].sendPacket(['dimChange', 'gridSize', parseInt(i.gridsize) || 30]);
      clients[target].sendPacket(['dimChange', 'backgroundColor', /#[a-fA-F0-9]{6}/.test(i.bgcolor) ? i.bgcolor : '#CDCDCD']);
      clients[target].sendPacket(['dimChange', 'gridColor', /#[a-fA-F0-9]{6}/.test(i.gridcolor) ? i.gridcolor : '#C8C8C8']);
      return;
    };
  };
  ws.sendPacket([1, 'addNotification', `Dimension "${dim}" does not exist.`]);
});

Command.add('/purgedims', 'mod', (ws) => {
  let newdims = [];
  for (let i in dims) {
    if (dims[i].id == 'main') {
      newdims.push(dims[i]);
      continue;
    };
    let count = 0;
    for (let j in clients) {
      if (clients[j].dim == dims[i].id) count++;
    };
    if (count == 0) {
      ws.sendPacket([1, 'addNotification', `Purged dimension "${dims[i].id}."`]);
    } else {
      newdims.push(dims[i]);
    };
  };
  dims = newdims;
});

Command.add('/rdim (removedimension) <id>', 'none', (ws, id) => {
  newid = id.replace(/</g, '&lt;').replace(/>/g, '&gt;');
  if (newid == 'main') {
    ws.sendPacket([1, 'addNotification', 'You cannot delete the main dimension!']);
    return;
  };
  for (let i in dims) {
    if (dims[i].id === newid && dims[i].ip !== ws.ip && !ws.mod) {
        ws.sendPacket([1, 'addNotification', 'You cannot delete a dimension that you didn\'t create!']);
        return;
    };
  };
  for (let i in clients) {
    if (clients[i].dim === newid) {
      clients[i].sendPacket([1, 'addNotification', `The dimension you were in, "${clients[i].dim}", was deleted, so you are being moved to "${dims[0].id}".`]);
      clients[i].dim = 'main';
      clients[i].sendPacket(['removeExisting']);
      clients[i].sendPacket(['dimChange', 'gridSize', parseInt(dims[0].gridsize) || 30]);
      clients[i].sendPacket(['dimChange', 'backgroundColor', /#[a-fA-F0-9]{6}/.test(dims[0].bgcolor) ? dims[0].bgcolor : '#CDCDCD']);
      clients[i].sendPacket(['dimChange', 'gridColor', /#[a-fA-F0-9]{6}/.test(dims[0].gridcolor) ? dims[0].gridcolor : '#C8C8C8']);
    };
  };
  for (let i in dims) {
    if (dims[i].id === newid) {
      dims.splice(i, 1);
      ws.sendPacket([1, 'addNotification', `Successfully deleted dimension "${id}".`]);
      return;
    };
  };
  ws.sendPacket([1, 'addNotification', `Dimension "${id}" does not exist.`]);
});

Command.add('/vanish (v) <state?>', 'yt', (ws, state) => {
  if (state) {
    if (['1', 'true'].includes(state) || (state == 'toggle' && !ws.vanished)) {
      !ws.vanished ? ws.sendPacket([1, 'addNotification', 'Vanished.']) : ws.sendPacket([1, 'addNotification', 'You are already vanished!']);
      ws.vanished = true;
    } else {
      ws.vanished ? ws.sendPacket([1, 'addNotification', 'Unvanished.']) : ws.sendPacket([1, 'addNotification', 'You are not vanished!']);
      ws.vanished = false;
    };
  } else {
    !ws.vanished ? ws.sendPacket([1, 'addNotification', 'Vanished.']) : ws.sendPacket([1, 'addNotification', 'You are already vanished!']);
    ws.vanished = true;
  };
});

Command.add('/gname (getname) <target>', 'dev', (ws, target) => {
  ws.sendPacket([1, 'addNotification', clients[target].tank.name]);
});

Command.add('/namecolor (nc) <target> <color>', 'mod', (ws, target, color) => {
  if (clients[target] && !isNaN(parseInt(color))) clients[target].tank.nameColor = parseInt(color)
});

Command.add('/ncg (namecolorgradient) <target> <hex1> <hex2>', 'mod', (ws, target, hex1, hex2) => {
  if (clients[target]) clients[target].tank.nameColor = [hex1, hex2];
});

Command.add('/tp <target> <x> <y>', 'admin', (ws, target, x, y) => {
  if (!isNaN(parseInt(x)) && !isNaN(parseInt(y))) {
    if (clients[target]) {
      clients[target].tank.x = parseInt(x);
      clients[target].tank.y = -parseInt(y);
    };
  };
});

Command.add('/sudo (say) (forcesay) <target> <message+>', 'admin', (ws, target, message) => {
  if (clients[target]) {
    if (clients[target].developer) {
      ws.sendPacket([1, 'addNotification', 'You can\'t sudo a developer, silly!']);
    } else {
      clients[target].lastChat = message;
    };
  };
});

Command.add('/name <target> <name+>', 'admin', (ws, target, name) => {
  if (clients[target]) {
    clients[target].tank.name = name;
    clients[target].sendPacket(['changeName', name]);
  };
});

Command.add('/showname (sname) (hasname) (hname) (hn) (sn) <target> <state>', 'none', (ws, target, state, targetObj) => {
  targetObj.showName = ['1', 'true'].includes(state);
});

Command.add('/overridetag (otag) <id>', 'dev', (ws, id) => {
  if (!isNaN(parseInt(id))) {
    ws.ranktag = Math.max(Math.min(parseInt(id), 5), 0);
    ws.sendPacket([1, 'addNotification', `Set rank tag to: ${{ 0: 'none', 1: '[YouTuber]', 2: '[Moderator]', 3: '[Admin]', 4: '[Developer]', 5: '[Featured Creator]' }[ws.ranktag]}.`]);
  };
});

Command.add('/visibleonleaderboard (onleaderboard) (vonlb) (vlb) (volb) (olb) (vonleaderboard) (vol) <target> <state?>', 'none', (ws, target, state, targetObj) => {
  state = state ?? '1';
  targetObj.tank.visibleOnLeaderboard = ['1', 'true'].includes(state);
});

const db = new sqlite3.Database('./database.db');

db.serialize(() => {
  db.run('CREATE TABLE IF NOT EXISTS banned_ips (id INTEGER PRIMARY KEY AUTOINCREMENT, ip TEXT UNIQUE)');
  db.run('CREATE TABLE IF NOT EXISTS ban_reasons (id INTEGER PRIMARY KEY AUTOINCREMENT, ip TEXT UNIQUE, reason TEXT)');
});

const complexity = function(body) {
  let gadgets = body.gadgets, layers = body.layers
  let c = 1
  if(layers) {
    for(let i=layers.length-1;i>=0;i--) {
      let layer = layers[i]
      if(layer) {
        if (layer.sides > 0) {
          c += layer.sides
        } else {
          c += layer.sides * -5
        };
      }
    }
  }
  if(gadgets) {
    for(let i=gadgets.length-1;i>=0;i--) {
      let gadget = gadgets[i]
      if(gadget && gadget.tank) {
        c += complexity(gadget.tank) + Math.abs(gadget.tank.outerSides || 0) + Math.abs(gadget.tank.sides || 0)
      }
    }
  }
  return c
}

process.on('uncaughtException', function (e) { console.log(e) })

var server = new WebSocketServer({
  port: 8080,
  maxPayload: 1024 * 1024 * 10 // 10 MB
});

var clients = {}
var bullets = []
var shapes = {}
var deadBullets = []
var deadShapes = {}
const getId = function() {
  let l = Math.max(...Object.keys({...clients, ...shapes}))
  if(!(l >= 0)) { l = -1 }
  for(let i=0;i<l;i++) {
    if(!(i in {...clients, ...shapes})) {
      return i
    }
  }
  return l + 1
}
const removeId = function(id, obj) {
  if(!obj || {...clients, ...shapes}[id] === obj) {
    if (clients[id]) {
      delete clients[id];
    } else {
      delete shapes[id];
    };
    updatePlayerCount();
  }
}

const dt = 50 / 3

Command.add('/deception <x> <y>', 'dev', (ws, x, y) => {
  const id = getId();
  shapes[id] = {
    sides: 3,
    x: parseFloat(x),
    y: -parseFloat(y),
    showName: true,
    ranktag: 0,
    level: 1,
    d: 0,
    radiant: 0,
    id: id,
    outerSides: 0,
    outerSize: 0,
    fadeType: [0, 2],
    size: 20,
    team: polygonStats[3].color,
    dim: ws.dim,
    hp: 35,
    maxHP: 35,
    score: Infinity,
    nameColor: 0,
    name: 'Eat Me',
    className: 'Eat Me',
    velocity: 0,
    damagers: {},
    isNew: true
  };
});

function summonPolygon(sides, x, y, radiant, dim, size = 1, velocity = 0, d = 0, team = null) {
  sides = sides != -3 ? Math.min(Math.max(sides, 3), 20) : -3;
  const id = getId();
  if (sides == -3) {
    shapes[id] = {
      sides: 3,
      x: x,
      y: y,
      showName: false,
      ranktag: 0,
      level: 1,
      d: d,
      radiant: radiant,
      id: id,
      outerSides: 0,
      outerSize: 0,
      fadeType: [0, 2],
      size: 45 * size,
      team: 2,
      dim: dim,
      health: 100,
      score: 0,
      nameColor: 6,
      name: 'Polyp',
      className: 'Polyp',
      velocity: velocity,
      polyp: true,
      damagers: {},
      isNew: true,
    };
    for (let d of dims) {
      if (d.id === dim) {
        d.quadtree.insert(id, shapes[id], 'shape');
        break;
      };
    };
    return;
  };
  const data = polygonStats[sides];
  const className = ({
    0: '',
    1: 'Radiant',
    2: 'Gleaming',
    3: 'Luminous',
    4: 'Lustrous',
    5: 'Highly Radiant'
  }[Math.max(Math.min(radiant, 5), 0)] + ' ' + data.name).trim()
  const radiantMultiplier = radiant == 0 ? 1 : 25 * 4 ** (radiant - 1);
  const health = 35 * 3.6 ** (sides - 3);
  shapes[id] = {
    sides: sides,
    x: x,
    y: y,
    showName: false,
    ranktag: 0,
    level: 1,
    d: d,
    radiant: radiant,
    id: id,
    outerSides: 0,
    outerSize: 0,
    fadeType: [0, 2],
    size: (20 * 1.5 ** (sides - 3)) * size, // Size Formula
    team: team ?? data.color,
    dim: dim,
    hp: health, // Health Formula (Above)
    maxHP: health,
    score: (250 * ((4 ** (sides - 2) - 1) / 3)) * radiantMultiplier, // XP Formula
    nameColor: 6,
    name: className,
    className: className,
    velocity: velocity,
    damagers: {},
    isNew: true
  };
  for (let d of dims) {
    if (d.id === dim) {
      d.quadtree.insert(id, shapes[id], 'shape');
      break;
    };
  };
};

Command.add('/summonpolygon (spawnpolygon) (summonpoly) (spawnpoly) (spoly) <sides> <x> <y> <radiant?>', 'dev', (ws, sides, x, y, radiant) => {
  summonPolygon(parseInt(sides), parseFloat(x), -parseFloat(y), radiant ?? 0, ws.dim);
});

const updatePlayerCount = function() {
  const count = Object.values(clients).reduce((value, item) => {
    return value + (item ? 1 : 0);
  }, 0);
  for (let i in clients) {
    let c = clients[i];
    c.sendPacket(['playercount', count - 1]);
  };
};

function handleBarrelReload(meID, meTank, mradDir = true) {
  
  function invertAngle(radians) {
    return -(radians - Math.PI);
  };
  function offset(x, y, forward, side, radians, size) {
    const cosRadians = Math.cos(radians);
    const sinRadians = Math.sin(radians);
    const forwardOffsetX = forward == 0 ? 0 : (forward * size) * sinRadians;
    const forwardOffsetY = forward == 0 ? 0 : (forward * size) * cosRadians;
    const sideOffsetX = side == 0 ? 0 : (side * size) * cosRadians;
    const sideOffsetY = side == 0 ? 0 : (side * size) * -sinRadians;
    return [x + forwardOffsetX + sideOffsetX, y + forwardOffsetY + sideOffsetY];
  };
  function handleBarrels(stackdata, barrelData, shooting, barrels) {
    barrelData ||= [];
    if (barrels) for (let i = 0; i < barrels.length; i++) {
      barrelData[i] ||= { animTime: 0 };
      barrelData[i].reloadTime ??= 0;
      barrelData[i].delayTime ??= 0;
      barrelData[i].applyDelay ??= true;
      if (barrelData[i].reloadTime <= 0 && barrelData[i].delayTime <= 0) {
        barrelData[i].reloadTime = 0;
        barrelData[i].delayTime = 0;
        let shouldShoot = false;
        if (barrels[i].shootTrigger) {
          switch (barrels[i].shootTrigger) {
            default: // Normal and any that aren't programmed
              shouldShoot = shooting[1];
            case 1: // Inverse
              shouldShoot = !shooting[1];
              break;
            case 2: // Always
              shouldShoot = true;
              break;
            case 3: // Never
              shouldShoot = false;
              break;
          };
        } else {
          shouldShoot = shooting[1];
        };
        if (shouldShoot) {
          if (barrelData[i].applyDelay) {
            barrelData[i].delayTime = (barrels[i].delay ?? 0) * barrels[i].reload;
            barrelData[i].applyDelay = false;
            if (barrelData[i].delayTime) continue;
          };
          let id = bullets.length;
          if (bulletIDs.includes(id)) {
            while (bulletIDs.includes(id)) id++;
          };
          bulletIDs.push(id);
          const barrelAngle = mradToRad(stackdata.rot) + barrels[i].rot;
          const invertedBarrelAngle = invertAngle(barrelAngle);
          let coords = offset(stackdata.cx, stackdata.cy, (barrels[i].distance ?? 0) + barrels[i].length * 2, -barrels[i].offset, invertedBarrelAngle, meTank.size * (stackdata.size || 1));
          /*
          Bullet Types:
          0 - Normal
          1 - Drone
          2 - Trap
          3 - Minion
          5 - Polyp Spawner
          7 - Rocket
          8 - Custom Trap
          9 - Polygon Spawner
          */
          if (barrels[i].type != 6) {
            let bullet = {
              type: barrels[i].type,
              radiant: meTank.radiant,
              size: barrels[i].width * meTank.size * (stackdata.size || 1) * (barrels[i].size || 1),
              x: coords[0],
              y: coords[1],
              fadeType: [0, 1],
              d: barrelAngle + degToRad(Math.round(Math.random() * ((barrels[i].spread || 0) * 2)) - (barrels[i].spread || 0)),
              parentID: meID,
              team: barrels[i].team ?? meTank.team,
              outerSize: barrels[i].type == 7 || barrels[i].type == 8 || barrels[i].type == 3 ? barrels[i].minion.outerSize : 0,
              outerSides: barrels[i].type == 7 || barrels[i].type == 8 || barrels[i].type == 3 ? barrels[i].minion.outerSides : 0,
              sides: barrels[i].type == 2 ? 4 : (barrels[i].type == 1 ? 3 : (barrels[i].type == 7 || barrels[i].type == 8 || barrels[i].type == 3 ? barrels[i].minion.sides : 0)),
              speed: barrels[i].speed ?? 1,
              id: id,
              lifetime: barrels[i].lifetime ?? 1,
              barrelData: [],
              gadgetData: [],
              parentData: {
                dim: clients[meID].dim
              },
              minDist: barrels[i].minDist || 0,
              maxDist: barrels[i].maxDist || 0,
              damage: barrels[i].damage,
              isNew: true
            };
            if ([0, 2, 5, 7, 8, 9].includes(barrels[i].type)) {
              if (barrels[i].type == 9) {
                summonPolygon(Math.floor(Math.random() * (barrels[i].maxSize - barrels[i].minSize + 1)) + barrels[i].minSize, bullet.x, bullet.y, barrels[i].radiant, clients[meID].dim, barrels[i].size, bullet.speed, invertedBarrelAngle, barrels[i].colorType == 0 ? null : clients[meID].tank.team);
              } else if (barrels[i].type == 5) {
                summonPolygon(-3, bullet.x, bullet.y, 0, clients[meID].dim, barrels[i].size, bullet.speed, invertedBarrelAngle);
              } else {
                if (barrels[i].minion?.barrels) bullet.barrels = barrels[i].minion.barrels;
                if (barrels[i].minion?.gadgets) bullet.gadgets = barrels[i].minion.gadgets;
                if (barrels[i].minion?.layers) bullet.layers = barrels[i].minion.layers;
                bullets.push(bullet);
                for (let d of dims) {
                  if (d.id === clients[meID].dim) {
                    d.quadtree.insert('b' + id, bullet, 'bullet');
                    break;
                  };
                };
              };
            };
          };
          barrelData[i].reloadTime = barrels[i].reload;
          if (barrels[i].recoil ?? 1) {
            meTank.xv += -((barrels[i].recoil ?? 1) / 16) * Math.sin(invertedBarrelAngle);
            meTank.yv += -((barrels[i].recoil ?? 1) / 16) * Math.cos(invertedBarrelAngle);
          };
        } else {
          barrelData[i].applyDelay = true;
        };
      } else {
        barrelData[i].reloadTime -= 0.025; // You can tweak this reload interval if needed.
        barrelData[i].delayTime -= 0.025;
        if (barrelData[i].reloadTime > barrels[i].reload || barrelData[i].reloadTime < 0) barrelData[i].reloadTime = 0;
        if (barrelData[i].delayTime < 0) barrelData[i].delayTime = 0;
      };
      barrelData[i].animTime = barrelData[i].reloadTime / barrels[i].reload;
    };
  };
  handleBarrels({ cx: meTank.x, cy: meTank.y, rot: mradDir ? meTank.d : radToMrad(meTank.d) }, meTank.barrelData, meTank.shooting, meTank.barrels);
  meTank.gadgetData = meTank.gadgets || [];
  function handleGadgets(gadgetData, stackdata, shooting) {
    const startStackdata = JSON.stringify(stackdata);
    for (let i = 0; i < gadgetData.length; i++) {
      let gadget = gadgetData[i];
      gadget.animTime = 0;
      if (gadget.type === 3 && gadget.tank) {
        stackdata.size ??= 1;
        let rot = mradToRad(stackdata.rot);
        switch (gadget.rotationType) {
          case 0: // Static
            rot = gadget.baseRot + mradToRad(stackdata.rot);
            break;
          case 1: // Auto-Cannon
          case 4: // Point At Mouse
            rot = gadget.baseRot + mradToRad(stackdata.rot);
            break;
          case 3: // Conditional
          case 2: // Constant
            if (gadget.anchored == 0) {
              rot = gadget.baseRot + mradToRad(stackdata.rot);
            } else {
              rot = gadget.baseRot;
            };
            if (gadget.rotationSpeed) rot += Math.PI * 2 + ((performanceNow() * 1.2) / 3000) * gadget.rotationSpeed;
        };
        let coords = offset(stackdata.cx, stackdata.cy, -gadget.offsetY, -gadget.offsetX, invertAngle(gadget.baseRot + mradToRad(stackdata.rot)), meTank.size * stackdata.size);
        stackdata.cx = coords[0];
        stackdata.cy = coords[1];
        stackdata.rot = radToMrad(rot);
        stackdata.size *= gadget.width;
        handleBarrels(stackdata, gadget.tank.barrels, shooting, gadget.tank.barrels);
        handleGadgets(gadget.tank.gadgets || [], stackdata, shooting);
      };
      stackdata = JSON.parse(startStackdata);
    };
  };
  handleGadgets(meTank.gadgetData, { cx: meTank.x, cy: meTank.y, rot: mradDir ? meTank.d : radToMrad(meTank.d) }, meTank.shooting);
};

const tick = function() {
  let start = performance.now()
  let data = [0, 0, [], [], [], []]
  let allWeapons = [], allBodies = []
  for(let i in clients) {
    let c = clients[i], meTank = c.tank
    if(meTank) {
      if(c.lastChat) {
        if (c.lastChat[0] !== '/') {
          data[5].push([
            c.clientId * 1,
            c.lastChat.slice(0, 500)
          ])
        };
        c.lastChat = false
      }
      if(c.weaponUpdate) {
        c.weaponUpdate = false
        data[3].push([
          c.clientId * 1,
          c.currentWeapon
        ])
      }
      allWeapons.push([
        c.clientId * 1,
        c.currentWeapon
      ])
      if(c.bodyUpdate) {
        c.bodyUpdate = false
        if (meTank.level != meTank.previousLevel) {
          meTank.xpToNextLevel = getXPToNextLevel(meTank.level);
          meTank.score = 0;
          meTank.totalScore = getXPToNextLevel(meTank.level - 1);
          meTank.previousLevel = meTank.level;
        };
        data[4].push([
          c.clientId * 1,
          c.currentBody
        ])
      }
      allBodies.push([
        c.clientId * 1,
        c.currentBody
      ]);
      if (c.mod || c.baccess) handleBarrelReload(c.clientId, meTank)
      meTank.xv += meTank.xa * dt
      meTank.yv += meTank.ya * dt
      meTank.x += meTank.xv * dt
      meTank.y += meTank.yv * dt
      meTank.xv *= 0.95
      meTank.yv *= 0.95
      let mapSize = 6000;
      for (let i of dims) {
        if (i.id === c.dim) {
          mapSize = i.mapsize;
          break;
        };
      };
      if(meTank.x > mapSize) { meTank.x = mapSize; meTank.xv = 0 }
      else if(meTank.x < -mapSize) { meTank.x = -mapSize; meTank.xv = 0 }
      if(meTank.y > mapSize) { meTank.y = mapSize; meTank.yv = 0 }
      else if(meTank.y < -mapSize) { meTank.y = -mapSize; meTank.yv = 0 }
      data[2].push([
        c.clientId * 1,
        Math.round(meTank.x),
        Math.round(meTank.y),
        Math.round(meTank.size),
        meTank.level,
        meTank.d,
        meTank.name,
        meTank.typing,
        meTank.nameColor,
        c.vanished,
        c.ranktag,
        meTank.barrelData,
        meTank.gadgetData,
        meTank.visibleOnLeaderboard,
        meTank.totalScore,
        meTank.score
      ])
    }
  }
  let _dt = performance.now() - start
  data.push(_dt)
  for(let i in clients) {
    let c = clients[i]
    data[1] = c.clientId * 1
    function removeDims(arr) {
      let newarr = [];
      for (let j in arr) {
        if ((arr[j].parentData?.dim || arr[j].dim) === c.dim) {
          newarr.push(arr[j]);
        };
      };
      return newarr;
    };
    function filterData(data, type = 'array', update = []) {
      const output = type == 'array' ? [] : {};
      for (let i in data) {
        const obj = data[i];
        if (obj.isNew) {
          if (type == 'array') output.push(obj);
          else output[obj || 0] = obj;
          continue;
        };
        const filtered = {};
        for (let key in obj) {
          if (update.includes(key)) filtered[key] = obj[key];
        };
        if (Object.keys(filtered).length > 0) {
          if (type == 'array') {
            output.push(filtered);
          } else {
            output[obj.id || 0] = filtered;
          };
        };
      };
      return type == 'array' ? output : Object.values(output);
    };
    function removeAndRestrict(arr, restrict = false) {
      let newarr = [];
      for (let j of arr) {
        const client = clients[j[0]];
        if (client.dim === c.dim) {
          const tank = client.tank;
          if (tank && restrict) {
            function limit(tank) {
              if (tank.auras) {
                tank.auras = tank.auras.slice(0, 50);
                for (let aura of tank.auras) {
                  if (Math.abs(aura.sides) > 50) {
                    if (aura.sides < 0) {
                      aura.sides = -50;
                    } else {
                      aura.sides = 50;
                    };
                  };
                };
              };
              if (tank.barrels) tank.barrels = tank.barrels.slice(0, 50);
              if (tank.layers) tank.layers = tank.layers.slice(0, 50);
              if (tank.gadgets) {
                tank.gadgets = tank.gadgets.slice(0, 50);
                for (let gadget of tank.gadgets) {
                  if (gadget.type === 3) {
                    limit(gadget.tank);
                  };
                };
              };
            };
            limit(tank);
          };
          newarr.push(j);
        };
      };
      return newarr;
    };
    if(c.isNew) {
      let sentWeapons = removeAndRestrict(allWeapons, false);
      let sentBodies = limit(removeAndRestrict(allBodies, false));
      let sentData2 = removeAndRestrict(data[2]);
      c.sendPacket([
        data[0],
        data[1],
        sentData2,
        sentWeapons,
        sentBodies
      ])
      c.isNew = false
      const sentBullets = removeDims(bullets);
      const sentShapes = removeDims(shapes);
      if (sentBullets.length > 0) c.sendPacket(['blt', sentBullets]);
      if (sentShapes.length > 0) c.sendPacket(['poly', sentShapes]);
    } else {
      let sentData = data.slice();
      sentData[2] = removeAndRestrict(data[2]);
      sentData[3] = removeAndRestrict(data[3], false);
      sentData[4] = limit(removeAndRestrict(data[4], false));
      sentData[5] = removeAndRestrict(data[5]);
      c.sendPacket(sentData)
      const sentBullets = filterData(removeDims(bullets), 'array', ['x', 'y', 'barrelData', 'gadgetData', 'id']);
      const sentShapes = filterData(removeDims(shapes), 'object', ['hp', 'x', 'y', 'd', 'id']);
      if (sentBullets.length + deadBullets.length > 0) c.sendPacket(['blt', [...sentBullets, ...deadBullets]]);
      if (Object.keys({ ...sentShapes, ...deadShapes }).length > 0) c.sendPacket(['poly', {...sentShapes, ...deadShapes}]);
    }
  }
  for (let bullet of bullets) bullet.isNew = false;
  for (let id in shapes) shapes[id].isNew = false;
  for (let i in deadBullets) deadBullets.splice(i, 1);
  for (let id in deadShapes) delete deadShapes[id];
}

const update = function(meTank, currentWeapon, currentBody, nolimit = false) {
  meTank.barrels = currentWeapon.barrels
  meTank.gadgets = currentBody.gadgets
  meTank.auras = currentBody.auras
  meTank.layers = currentBody.layers
  meTank.outerSides = currentBody.outerSides
  if(meTank.outerSides > 100 && !nolimit) { meTank.outerSides = 100 }
  if(meTank.outerSides < -100 && !nolimit) { meTank.outerSides = -100 }
  meTank.outerSize = currentBody.outerSize
  if(meTank.outerSize > 100 && !nolimit) {meTank.outerSize = 100} 
  meTank.sides = currentBody.sides
  if(meTank.sides > 100 && !nolimit) { meTank.sides = 100 }
  if(meTank.sides < -100 && !nolimit) { meTank.sides = -100 }
  meTank.radiant = currentBody.radiant
  if(meTank.radiant > 25 && !nolimit) { meTank.radiant = 25 }
  meTank.cameraSizeMultiplier = currentWeapon.cameraSizeMultiplier * currentBody.cameraSizeMultiplier
  meTank.isCelestial = currentBody.type ? true : false
  meTank.team = currentBody.team
  meTank.level = currentBody.level
  meTank.size = 30 * currentBody.size * Math.pow(1.01, meTank.level - 1)
  if(meTank.size > 500 && !nolimit) { meTank.size = 500 }
  meTank.barrelData ||= []
  meTank.gadgetData ||= []
}

function updateBullets() {
  function invertAngle(radians) {
    return -(radians - Math.PI);
  };
  for (let bullet of bullets) {
    let owner = clients[bullet.parentID];
    if (!owner) {
      bullet.lifetime = 0;
    };
    let thisDim = {};
    for (let d of dims) {
      if (owner.dim == d.id) {
        thisDim = d;
        break;
      };
    };
    let angle = invertAngle(bullet.d);
    if (bullet.type == 7 || bullet.type == 8 || bullet.type == 3) {
      bullet.shooting = { 1: true, 2: false, 3: false };
      bullet.xv ||= 0;
      bullet.yv ||= 0;
      handleBarrelReload(bullet.parentID, bullet, false);
    };
    if (bullet.lifetime) switch (bullet.type) {
      case 7: // Rocket
      case 0: // Normal
        bullet.x += (bullet.speed * speedMult) * Math.sin(angle) + (bullet.xv || 0);
        bullet.y += (bullet.speed * speedMult) * Math.cos(angle) + (bullet.yv || 0);
        break;
      case 8: // Custom Trap
      case 2: // Trap
        bullet.velocity ??= bullet.speed * speedMult;
        if (bullet.velocity > 0) {
          bullet.velocity -= 0.05;
          if (bullet.velocity < 0) bullet.velocity = 0;
        };
        bullet.x += bullet.velocity * Math.sin(angle) + (bullet.xv || 0);
        bullet.y += bullet.velocity * Math.cos(angle) + (bullet.yv || 0);
        break;
      case 3: // Minion Spawner
      case 1: // Drone
        const shooting = owner.tank.shooting && owner.tank.shooting[1];
        const rightClicking = owner.tank.shooting && owner.tank.shooting[3];
        const maxDist = shooting && !rightClicking ? bullet.maxDist : (rightClicking ? 0 : owner.tank.size + 15);
        const minDist = shooting && !rightClicking ? bullet.minDist : (rightClicking ? 0 : owner.tank.size + 15);
        const coordinates = {
          x: shooting || rightClicking ? (isNaN(owner.tank.mouseX) ? 0 : owner.tank.mouseX) : owner.tank.x,
          y: shooting || rightClicking ? (isNaN(owner.tank.mouseY) ? 0 : owner.tank.mouseY) : -owner.tank.y
        };
        let targetAngle = Math.atan2(coordinates.y + bullet.y, coordinates.x - bullet.x) + (Math.PI / 2);
        const inMin = inDistance([bullet.x, bullet.y], [coordinates.x, coordinates.y], minDist * bullet.size);
        const inMax = inDistance([bullet.x, bullet.y], [coordinates.x, coordinates.y], maxDist * bullet.size);
        if (inMax && !inMin) {
          targetAngle -= Math.PI / 2;
        };
        if (rightClicking || inMin) targetAngle += Math.PI;
        bullet.d = invertAngle(targetAngle);
        bullet.x += (bullet.speed * speedMult) * Math.sin(targetAngle) + (bullet.xv || 0);
        bullet.y += (bullet.speed * speedMult) * Math.cos(targetAngle) + (bullet.yv || 0);
        bullet.lifetime = 1;
    }
    bullet.lifetime -= 0.01; // Tweak if needed.
    thisDim.quadtree.updateObject('b' + bullet.id, bullet);
    if (bullet.lifetime <= 0) {
      for (let i in bullets) {
        if (bullets[i].id == bullet.id) {
          const dead = bullets[i];
          dead.dead = true;
          deadBullets.push(dead);
          thisDim.quadtree.remove('b' + bullet.id);
          bullets.splice(i, 1);
          break;
        };
      };
    };
  };
};
function random(min, max) {
  return Math.floor(Math.random() * (max - min + 1)) + min;
};
function biasedRandom(bias, min, max) {
  const biased = Math.random() ** bias;
  return Math.floor(biased * (max - min + 1)) + min;
};
function updateShapes() {
  for (let dim of dims) {
    let shapeCount = 0;
    for (let i in shapes) {
      if (shapes[i].dim == dim.id) shapeCount++;
    };
    dim.full ??= false;
    if (shapeCount < 100 * dim.shapemult && !dim.full) {
      let radiantAmount = 0;
      const baseChance = 4096;
      while (true) {
        const chance = 1 / (baseChance * 16 ** radiantAmount);
        if (Math.random() > chance) {
          break;
        };
        radiantAmount++;
        if (radiantAmount >= 20) {
          break;
        };
      };
 //     summonPolygon(biasedRandom(6, 3, 13), random(-dim.mapsize, dim.mapsize), random(-dim.mapsize, dim.mapsize), radiantAmount, dim.id);
    } else {
      if (shapeCount >= 100 * dim.shapemult) {
        dim.full = true;
      } else if (dim.full === true) {
        dim.full = 100;
      } else {
        dim.full--;
        if (dim.full <= 0) {
          dim.full = false;
        };
      };
    };
  };
  for (let i in shapes) {
    let inDim = false;
    let thisDim = {};
    for (let dim of dims) {
      if (dim.id == shapes[i].dim) {
        inDim = true;
        thisDim = dim;
        break;
      };
    };
    if (!inDim) {
      const dead = shapes[i];
      dead.dead = true;
      deadShapes[i] = dead;
      delete shapes[i];
      continue;
    };
    const shape = shapes[i];
    const scaleDivision = shape.size / 10;
    shape.d += 0.025 / scaleDivision;
    if (shape.velocity > 0) shape.velocity -= 0.025;
    if (shape.velocity < 0) shape.velocity = 0;
    let speed = 1;
    if (shape.polyp) speed = 2;
    const quadBullets = thisDim.quadtree.getNearObjects(shape.id, 'bullet').reduce((ids, item) => [...ids, item.obj.id], []);
    for (let bullet of bullets) {
      if (!quadBullets.includes(bullet.id)) continue;
      if (bullet.parentData.dim != shape.dim) continue;
      if (inDistance([bullet.x, bullet.y], [shape.x, shape.y], shape.size + bullet.size)) { // Calculates if the shape and bullet are colliding.
        const damageMult = clients[bullet.parentID] ? globalDamageMult + clients[bullet.parentID].currentBody.level : globalDamageMult;
        shape.hp -= bullet.damage * damageMult;
        if (clients[bullet.parentID]) if (shape.damagers[bullet.parentID]) {
          shape.damagers[bullet.parentID] += bullet.damage * damageMult;
        } else {
          shape.damagers[bullet.parentID] = bullet.damage * damageMult;
        };
      };
    };
    for (let j in clients) {
      const player = clients[j];
      if (player.dim != shape.dim) continue;
      if (inDistance([player.tank.x, player.tank.y], [shape.x, shape.y], shape.size + player.tank.size)) {
        const damageMult = globalDamageMult + player.currentBody.level;
        shape.hp -= player.currentBody.bodyDamageMultiplier * damageMult;
        const distance = (shape.size - Math.sqrt((player.tank.x - shape.x) ** 2 + (player.tank.y - shape.y) ** 2)) / 5000;
        const direction = Math.atan2(player.tank.y - shape.y, player.tank.x - shape.x);
        player.tank.xv += distance * Math.sin(direction);
        player.tank.yv += distance * Math.cos(direction);
        if (shape.damagers[j]) {
          shape.damagers[j] += player.currentBody.bodyDamageMultiplier * damageMult;
        } else {
          shape.damagers[j] = player.currentBody.bodyDamageMultiplier * damageMult;
        };
      };
    };
    if (shape.hp <= 0) {
      for (let id in shape.damagers) {
        if (!clients[id]) continue;
        const damageInflicted = shape.damagers[id];
        const damageRatio = Math.min(damageInflicted / shape.maxHP, 1);
        clients[id].tank.totalScore += shape.score * damageRatio;
        clients[id].tank.score += shape.score * damageRatio;
        if (clients[id].tank.score >= clients[id].tank.xpToNextLevel) {
          while (clients[id].tank.score >= clients[id].tank.xpToNextLevel) {
            clients[id].currentBody.level++;
            clients[id].tank.score -= clients[id].tank.xpToNextLevel;
            clients[id].tank.xpToNextLevel = getXPToNextLevel(clients[id].currentBody.level);
          };
        };
        clients[id].tank.previousLevel = clients[id].currentBody.level;
        update(clients[id].tank, clients[id].currentWeapon, clients[id].currentBody, clients[id].nolimit);
        clients[id].bodyUpdate = true;
      };
      const dead = shapes[i];
      dead.dead = true;
      deadShapes[i] = dead;
      thisDim.quadtree.remove(shape.id);
      delete shapes[i];
      continue;
    };
    shape.x += ((speedMult * speed) / scaleDivision + shape.velocity) * Math.sin(shape.d) + (shape.xv || 0);
    shape.y += ((speedMult * speed) / scaleDivision + shape.velocity) * Math.cos(shape.d) + (shape.yv || 0);
    thisDim.quadtree.updateObject(i, shape);
  };
};

setInterval(updateBullets, dt);
setInterval(updateShapes, dt);
setInterval(tick, dt)
setInterval(bancheck, dt * 50);
setInterval(multiboxcheck, dt * 500);

function bancheck() {
  try {
    for (let i in clients) {
      const c = clients[i];
      db.get('SELECT b.ip, COALESCE(r.reason, "None Provided") AS reason FROM banned_ips b LEFT JOIN ban_reasons r ON b.ip = r.ip WHERE b.ip = ?', [sha256(c.ip)], (err, row) => {
        if (err) {
          console.error(err);
        };
        if (row) {
          console.log(`Kicked IP ${sha256(c.ip)} on ban check.`);
          c.sendPacket(['banMessage', `You were banned!<br>Reason: ${row.reason}<br><br>Join Acrocord at https://discord.gg/5SWwubeDUS if you wish to appeal this ban!<br><br>Ban ID: ${sha256(c.ip)}`]);
          c.close(); // Banned IP
        };
      });
      db.get('SELECT b.ip, COALESCE(r.reason, "None Provided") AS reason FROM banned_ips b LEFT JOIN ban_reasons r ON b.ip = r.ip WHERE b.ip = ?', [encryptIP(c.ip)], (err, row) => {
        if (err) {
          console.error(err);
        };
        if (row) {
          console.log(`Kicked IP ${encryptIP(c.ip)} on ban check.`);
          c.sendPacket(['banMessage', `You were banned!<br>Reason: ${row.reason}<br><br>Join Acrocord at https://discord.gg/5SWwubeDUS if you wish to appeal this ban!<br><br>Ban ID: ${encryptIP(c.ip)}`]);
          c.close(); // Banned IP
        };
      });
    };
  } catch (e) {
    console.error(e);
  };
};

function multiboxcheck() { // Do not run often, can slow down performance.
  for (let i in clients) {
    const data = JSON.stringify(clients[i].commandlog.slice(-10));
    for (let j in clients) {
      if (j == i) continue;
      const data2 = JSON.stringify(clients[j].commandlog.slice(-10));
      if (data === data2 && data != '[]') {
        clients[i].tank = 0;
        clients[i].sendPacket(['kickMessage', 'You were kicked for multiboxing! (Experimental Feature)']);

        clients[j].tank = 0;
        clients[j].sendPacket(['kickMessage', 'You were kicked for multiboxing! (Experimental Feature)']);
        console.log(`Detected multibox: [${i}, ${j}]`);
        break;
      };
    };
  };
};

async function main() {
  try {

    const existingIPs = {};

    server.on("connection", async (ws, request) => {
      ws.on("close", () => {
        console.log("disconnect")
        updatePlayerCount();
        existingIPs[ip] <= 1 ? delete existingIPs[ip] : existingIPs[ip] -= 1;
        if (ws.inPrivate) {
            for (let i of dims) {
                if (ws.dim === i.id) {
                    let count = -1;
                    for (let j in clients) {
                        if (clients[j].dim === ws.dim) {
                            count++;
                        };
                    };
                    if (count <= 0) {
                        for (let j in dims) {
                            if (dims[j].id === ws.dim) {
                                dims.splice(j, 1);
                                break;
                            };
                        };
                    };
                };
            };
        };
        removeId(ws.clientId, ws)
      })
      const getIP = () => {
        const ip = String((request.headers['x-forwarded-for'] || request.socket.remoteAddress).split(',')[0]);
        return ip;
      };
      const ip = getIP();

      const ban = (reason) => {
        db.run('INSERT INTO banned_ips (ip) VALUES (?)', [encryptIP(getIP())], err => {
        if (err) {
            return false;
        };
        db.run('INSERT INTO ban_reasons (ip, reason) VALUES (?, ?)', [encryptIP(getIP()), reason], err => {
            if (err) {
                console.error(err);
                return false;
            } else {
                ws.close();
                return true;
            };
        });
        });
      };

      ws.ban = ban;

      const url = `https://v2.api.iphub.info/ip/${ip}`;
      if (ip !== '192.168.101.170') { // 62.212.64.17 - aeiou vpn
        axios.get(url, {
          headers: {
            'X-Key': process.env.IPHUBKEY
          }
        }).then(response => {
          const block = response.data.block;
          if (block === 1) {
            ws.sendPacket(['kickMessage', 'You must disable your VPN to enter this game!', 'VPN DETECTED (Automatic)']);
            ws.close();
          };
        }).catch(err => {
          console.error(err);
        });
      };

      if (existingIPs[ip]) {
        existingIPs[ip] += 1;
      } else {
        existingIPs[ip] = 1;
      };
      if (existingIPs[ip] > 2) {
        console.log(`Kicked ip (more than 2 found).`)
        ws.close() // 2 Tabs Maximum
      };

      console.log('connect')
      const rho = request.headers.origin;
      ws.sendPacket = function(packet) {
        ws.send(pack(packet))
      }
      if (rho.includes('test.acropolis.ac') || rho.includes('admin.acropolis.ac')) {
        console.log('join');
      } else {
        console.log('kicked socket for header fail');
        ws.sendPacket(['log', 'Incorrect Link', 'red']);
        ws.close();
        return;
      };
      ws.sendPacket(['newPerformance', performanceNow()]);
      ws.clientId = getId();
      clients[ws.clientId] = ws
      clients[ws.clientId].ip = ip;
      ws.currentWeapon = {
        cameraSizeMultiplier: 1,
        maxDrones: 0,
        name: "node",
        barrels: []
      }
      ws.currentBody = {
        cameraSizeMultiplier: 1,
        gadgets: [],
        layers: [],
        sides: 0,
        outerSides: 0,
        outerSize: 0,
        healthMultiplier: 1,
        bodyDamageMultiplier: 1,
        speedMultiplier: 1,
        maxDrones: 0,
        name: "base",
        type: 0,
        level: 1,
        size: 1,
        radiant: 0,
        team: 0,
        overrideTankName: ""
      }
      ws.commandlog = [];
      ws.inPrivate = false;
      ws.on("message", async (data) => {
        let type = 0
        try {
          if(data.length > 2000000) {
            ws.close()
            return
          }
          data = unpack(data)
          if(!data) { return }
          type = data.splice(0, 1)[0]
        } catch (e) {
          return
        }
        switch(type) {
          case 'admin': {
            if (ws.onAdminAcro) break;
            if (sha256(data[0]) === '06edd04eb47f450b398e68e381192e8b989f45a660b43d4ef0f07e4b47473348') {
              ws.sendPacket(['accepted']);
              ws.onAdminAcro = true;
            } else {
              ws.sendPacket(['rejected']);
              ws.close();
            };
            break;
          };
          case 'adminCommand': {
            if (!ws.onAdminAcro) break;
            const parameters = [];
            let type = 'normal';
            let value = '';
            let escapedString = false;
            for (let i = 0; i < data[0].length; i++) {
                switch (type) {
                    case 'normal': {
                        if (data[0][i] == ' ') {
                            parameters.push(value);
                            if (data[0][i + 1] == '"' || data[0][i + 1] == "'") {
                                type = 'string';
                                escapedString = false;
                            };
                            value = '';
                        } else {
                            value += data[0][i];
                        };
                        break;
                    }
                    case 'string': {
                        if (!escapedString && value.length > 1 && data[0][i - 1] == value[0]) {
                            parameters.push(value.slice(1, value.length - 1));
                            type = 'normal';
                            if (data[0][i + 1] == '"' || data[0][i + 1] == "'") {
                                type = 'string';
                                escapedString = false;
                            };
                            value = '';
                        } else if (data[0][i] != '\\' || escapedString) {
                            value += data[0][i];
                        } else {
                            escapedString = true;
                        };
                    }
                };
            };
            if (value) parameters.push(type == 'normal' ? value : value.slice(1, value.length - 1));
            const cmd = parameters.splice(0, 1)[0];
            switch (cmd) {
                case 'help': {
                    ws.sendPacket(['log', `
                        help - Shows list of terminal commands.<br>
                        exec [command] - Runs [command] ingame.
                    `, 'white']);
                    break;
                };
                case 'exec': {
                    const cmdName = parameters[0].split(' ')[0];
                    try {
                        Command.execute({
                            sendPacket: function(data) {
                                if (data[0] == 1 && data[1] == 'addNotification') {
                                    ws.sendPacket(['log', data[2]
                                        .replaceAll('&', '&amp;')
                                        .replaceAll('<', '&lt;')
                                        .replaceAll('>', '&gt;')
                                    ]);
                                };
                            },
                            yt: true,
                            mod: true,
                            admin: true,
                            developer: true
                        }, cmdName, parameters[0].split(' ').slice(1));
                        ws.sendPacket(['log', 'Finished executing command.']);
                    } catch {
                        ws.sendPacket(['log', `Something went wrong whilst trying to execute command ${cmdName}`, 'red']);
                    };
                    break;
                };
            };
            break;
          };
          case 'joingame': {
            updatePlayerCount();
            ASPB.forEach(name => {
                if ((data[2] || '').includes(name)) {
                    ban(`This is an ASPB (Automatic Serverside Purge Ban). If you feel this is a false ban, submit an appeal.`);
                };
            });
            ws.sendPacket(['removeExisting']);
            ws.resetLevel = true;
            ws.developer = false;
            ws.admin = false;
            ws.mod = false;
            ws.vanished = false;
            ws.nolimit = false;
            ws.throttle = 0;
            ws.sendPacket(['dimChange', 'gridSize', parseInt(dims[0].gridsize) || 30]);
            ws.sendPacket(['dimChange', 'backgroundColor', /#[a-fA-F0-9]{6}/.test(dims[0].bgcolor) ? dims[0].bgcolor : '#CDCDCD']);
            ws.sendPacket(['dimChange', 'gridColor', /#[a-fA-F0-9]{6}/.test(dims[0].gridcolor) ? dims[0].gridcolor : '#C8C8C8']);
            setInterval(() => {
              if (ws.throttle > 0) ws.throttle--;
            }, 10);
            ws.sendPacket(['rank', false]);
            ws.ranktag = 0;
            ws.dim = 'main';
            ws.tank = {
              mouseX: 0,
              mouseY: 0,
              x: Math.round(data[0]) || 0,
              y: Math.round(data[1]) || 0,
              d: 0,
              xv: 0,
              yv: 0,
              xa: 0,
              ya: 0,
              previousLevel: 1,
              level: 1,
              name: (data[2] || '').slice(0, 50),
              typing: false,
              shooting: {},
              nameColor: 6,
              visibleOnLeaderboard: true,
              score: data[3] || 0,
              totalScore: data[3] || 0,
              xpToNextLevel: 100
            };
            if (ws.tank.score >= ws.tank.xpToNextLevel) {
              while (ws.tank.score >= ws.tank.xpToNextLevel) {
                ws.currentBody.level++;
                ws.tank.score -= ws.tank.xpToNextLevel;
                ws.tank.xpToNextLevel = getXPToNextLevel(ws.currentBody.level);
              };
            };
            ws.tank.previousLevel = ws.currentBody.level;
            update(ws.tank, ws.currentWeapon, ws.currentBody, ws.nolimit);
            ws.sendPacket([12, 'popup', '300 members thing heh', 'WE HAVE REACHED 300 MEMBERS! as a sign of appreciation we are gonna focus on adding features to the game. (CONDITIONALS SOON!) join the discord server: https://discord.gg/7DcTkVT4sk'])
            ws.isNew = true
            break
          }
          case 'shooting': {
            if (ws.tank) ws.tank.shooting = data[0];
            break;
          }
          case 'mouse': {
            if (ws.tank) {
              ws.tank.mouseX = data[0] + ws.tank.x;
              ws.tank.mouseY = -data[1] - ws.tank.y;
            };
            break;
          }
          case 'typing': {
            if(ws.tank) {
              ws.tank.typing = data[0]
            }
            break
          }
          case 'move': {
            let t = ws.tank
            if(!t) { return }
            let x = data[0], y = data[1]
            let d = x * x + y * y
            ws.commandlog.push({
              t: Math.round(Date.now() / 10),
              y: 'move',
              c: [x, y, d]
            });
            d = (d > 1 ? 1 / Math.sqrt(d) : 1) * 0.0016 * ws.currentBody.speedMultiplier * Math.pow(0.983, t.level - 1)
            t.xa = x * d
            t.ya = -y * d
            break
          }
          case 'd': {
            if(ws.tank) {
              ws.tank.d = data[0]
            }
            break
          }
          case 'weapon': {
            let weapon = data[0]
            try {
              update(ws.tank, weapon, ws.currentBody, ws.nolimit)
              ws.currentWeapon = weapon
              ws.weaponUpdate = true
            } catch(e) {}
            break
          }
          case 'body': {
            let body = data[0]
            try {
              if (ws.resetLevel) {
                body.level = ws.currentBody.level;
                ws.resetLevel = false;
              };
              let score = complexity(body)
              if(score > 500000 && !ws.nolimit) {
                ws.sendPacket([1, 'alert', `Calculated tank complexity index (${score}) was too high!`])
                console.log('calculated tank complexity index was too high:', score)
                break
              }
              update(ws.tank, ws.currentWeapon, body, ws.nolimit)
              ws.currentBody = body
              ws.bodyUpdate = true
            } catch(e) {}
            break
          };
          case 'chat': {
            if (!ws.throttle || ws.admin) {
              let d = data[0];
              badWords.forEach(word => {
                let filtered = word;
                letterConversions.forEach(conversion => {
                  filtered = filtered.replace(new RegExp(conversion.original, 'ig'), m => `[${m}${conversion.converted}]`);
                });
                d = d.replace(new RegExp(filtered, 'ig'), m => '#'.repeat(m.length));
              });
              if (d[0] == '/') {
                let params = d.split(' ');
                let cmd = params.splice(0, 1)[0];
                Command.execute(ws, cmd, params);
              } else {
                ws.throttle = 25;
              };
              ws.lastChat = d;
            } else {
              ws.sendPacket([1, 'addNotification', 'Slow down in chat!']);
            };
            break
          }
          case 'token': {
            let t = data[0] ? sha256(data[0]) : '';
            if (t === process.env.developerToken) {
              console.log(`Token Joined: [Developer] ${ws.tank.name} ${encryptIP(ws.ip)}`);
              ws.developer = true;
              ws.admin = true;
              ws.mod = true;
              ws.yt = true;
              ws.nolimit = true;
              ws.tank.nameColor = 127;
              ws.ranktag = 4
              ws.sendPacket(['rank', true]);
            } else if (t === process.env.adminToken) {
              console.log(`Token Joined: [Admin] ${ws.tank.name} ${encryptIP(ws.ip)}`);
              ws.admin = true;
              ws.mod = true;
              ws.yt = true;
              ws.nolimit = true;
              ws.ranktag = 3
              ws.tank.nameColor = 128;
              ws.sendPacket(['rank', true]);
              // mod token
            } else if (t === "3a351d593f4ab4f5bae2ebf4eb49da30fa2c19b9ad93edf64d5f4315d1aff6e5") {
              console.log(`Token Joined: [Moderator] ${ws.tank.name} ${encryptIP(ws.ip)}`);
              ws.mod = true;
              ws.yt = true;
              ws.tank.nameColor = 129;
              ws.nolimit = true;
              ws.ranktag = 2
              ws.sendPacket(['rank', true]);
            } else if (t === process.env.ytToken) {
              console.log(`Token Joined: [YouTuber] ${ws.tank.name} ${encryptIP(ws.ip)}`);
              ws.yt = true;
              ws.nolimit = true;
              ws.tank.nameColor = 130;
              ws.ranktag = 1
              ws.sendPacket(['rank', true]);
            } else if (t === process.env.tankgalToken) {
              console.log(`Token Joined: [Moderator] ${ws.tank.name} ${encryptIP(ws.ip)}`);
              ws.mod = true;
              ws.yt = true;
              ws.tank.nameColor = 131;
              ws.ranktag = 2
              ws.sendPacket(['rank', true]);
              // fc token
            } else if (t === "7e8ab34459e502c8fd99d0e227e79fec016682c400f41165ec35e5f13a5d8b83") {
              console.log(`Token Joined: [Featured Creator] ${ws.tank.name} ${encryptIP(ws.ip)}`);
              ws.nolimit = true;
              ws.tank.nameColor = ['#3d70f2', '#a43df2'];
              ws.ranktag = 5;
            } else if (t === process.env.devHelperToken) {
              console.log(`Token Joined: [Developer Helper] ${ws.tank.name} ${encryptIP(ws.ip)}`);
              ws.nolimit = true;
              ws.admin = true;
              ws.mod = true;
              ws.yt = true;
              ws.tank.nameColor = ['#865CAE', '#7440C0'];
            } else if (t === process.env.specialToken) {
              ws.tank.nameColor = ['#FFBE00', '#FFCF3F'];
            };
          }
          default:
            break
        }  })
    })
  } catch (e) {
    console.error(e)
  };
};

main().catch(console.error);
