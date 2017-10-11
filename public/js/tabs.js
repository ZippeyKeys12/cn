'use_strict'

/* Generic Tab */
class Tab {
  constructor(title) {
    this.parent = null

    this.dom         = $('#tab-template').clone().contents()
    this.dom.content = $('<div class="tab-content"></div>')

    this.setTitle(title)
  }

  addEventListener() {
    this.dom.on('click', () => {
      this.setActive()
    })

    this.dom.children('.close').on('click', () => {
      if (this.parent)
        this.parent.remove(this)
    })

    this.dom.on('dragstart', (evt) => {
      if (ui) ui.currentView.draggedTab = this
      $('body').addClass('grabbing')
    })

    this.dom.on('dragend', (evt) => {
      $('body').removeClass('grabbing')
    })
  }

  setTitle (title) {
    this.title = title
    this.dom.children('.title').text(title)
  }

  setActive() {
    if (this.parent) {
      this.parent.clearSelection()
      this.parent.setActiveTab(this)
    }
    this.dom.addClass('active')
    this.dom.content.show()
    this.refresh()
  }

  clearSelection () {
    this.dom.removeClass('active')
    this.dom.content.hide()
  }

  isSelected () {
    this.dom.hasClass('active')
  }

  // Dummy methods to be overwriten
  refresh () {}
  mark (loc) {}
  clear ()   {}
  update ()  {}
  highlight() {}

}

/* Tab with SVG graph */
class TabGraph extends Tab {
  constructor(title) {
    super(title)

    this.dom.graph = $('#graph-template').clone().contents()
    this.dom.content.append(this.dom.graph)
    this.svg = null

    this.dom.graph.children('#minus').on('click', () => {
      this.svg.panzoom('zoom', true)
    })

    this.dom.graph.children('#reset').on('click', () => {
      this.svg.panzoom('resetZoom')
      this.svg.panzoom('resetPan')
    })

    this.dom.graph.children('#plus').on('click', () => {
      this.svg.panzoom('zoom');
    })
  }

  setValue(data) {
    // Remove previous one
    if (this.svg)
      this.svg.remove()

    // Add to the container
    this.dot = json_to_dot(data)
    this.dom.graph.children('.svg').append(Viz(this.dot))
    this.svg = this.dom.graph.find('svg')
    this.svg.panzoom()

    // Set active
    this.setActive()
    this.refresh()
  }
}

/* Tab with CodeMirror editor */
class TabEditor extends Tab {
  constructor(title, source) {
    super(title)
    this.dom.content.addClass('editor')

    this.editor = CodeMirror (this.dom.content[0], {
      styleActiveLine: true,
      lineNumbers: true,
      matchBrackets: true,
      tabSize: 2,
      smartIndent: true,
      lineWrapping: true
    })

    this.editor.on('blur', (doc) => {
      ui.currentView.highlight()
      this.skipCursorEvent = true
    })

    // CodeMirror overwrites 'click' events
    this.editor.on('mousedown', () => {
      ui.currentView.highlight()
      this.skipCursorEvent = true
    })

    this.editor.on('dblclick', (doc) => {
      this.skipCursorEvent = false
      this.markSelection(doc)
    })

    this.editor.on('viewportChange', (doc) => {
      //console.log('view port change')
    })

    this.editor.on('refresh', (doc) => {
      //console.log('refresh')
    })

    this.editor.on('update', (doc) => {
      //console.log('update')
    })



    if (source) this.editor.setValue(source)

    this.skipCursorEvent = true
  }

  getValue() {
    return this.editor.getValue()
  }

  setValue(value) {
    this.editor.setValue(value)
    this.setActive()
    this.refresh()
  }

  appendValue(value) {
    this.setValue(this.getValue()+value)
  }

  colorLines(i, e, color) {
    for (let k = i; k <= e; k++) {
      this.editor.removeLineClass(k, 'background')
      this.editor.addLineClass(k, 'background', 'color'+color)
    }
  }

  clear() {
    this.editor.eachLine((line) => {
      this.editor.removeLineClass(line, 'background')
    })
  }

  markSelection(doc) {
    // Just got focus or a click event
    if (this.skipCursorEvent) {
      this.skipCursorEvent = false
      return;
    }
    // If not dirty, then mark selection
    let from = doc.getCursor('from')
    let to   = doc.getCursor('to')
    ui.currentView.markSelection(this.getLocation(from, to))
  }

  refresh () {
    this.editor.refresh()
  }
}

/* ReadOnly Editor */
class TabReadOnly extends TabEditor {
  constructor (title) {
    super(title)
    this.editor.setOption ('readOnly', true)
  }
}

/* Tab C source */
class TabSource extends TabEditor {
  constructor(title, source) {
    super(title, source)
    this.editor.setOption('mode', 'text/x-csrc')
    this.editor.on('cursorActivity', (doc) => this.markSelection(doc))

    this.editor.on('change', () => {
      ui.currentView.dirty = true;
      //ui.currentView.clear()
    })
    // No close button
    this.dom.children('.close').hide()
  }

  getLocation(from, to) {
    let locations = ui.currentView.data.locs;
    for (let i = 0; i < locations.length; i++) {
      let loc = locations[i]
      if ((loc.c.begin.line < from.line ||
          (loc.c.begin.line == from.line && loc.c.begin.ch <= from.ch))
        && (loc.c.end.line > to.line ||
          (loc.c.end.line == to.line && loc.c.end.ch > to.ch)))
        return loc
    }
    return null
  }

  mark(loc) {
    this.editor.markText (loc.c.begin, loc.c.end, {className: getColor(loc.color)})
  }

  highlight() {
    let locations = ui.currentView.data.locs;
    for (let i = 0; i < locations.length; i++) {
      this.mark(locations[i])
    }
  }

  clear() {
    let marks = this.editor.getAllMarks()
    for (let i = 0; i < marks.length; i++)
      marks[i].clear()
  }
}

/* Tab Cabs */
class TabCabs extends TabReadOnly {
  constructor() {
    super('Cabs')
    this.editor.setOption('placeholder', '<Cabs elaboration failed...>')
  }

  update() {
    this.setValue(ui.currentView.data.cabs)
  }
}

/* Tab Cabs */
class TabAil extends TabReadOnly {
  constructor() {
    super('Ail')
    this.editor.setOption('placeholder', '<Ail elaboration failed...>')
  }

  update() {
    this.setValue(ui.currentView.data.ail)
  }
}



/* Tab Core */
class TabCore extends TabReadOnly {
  constructor () {
    super('Core')

    this.tooltip = $(document.createElement('div'))
    this.tooltip.addClass('tooltip')
    this.tooltip.appendTo(this.content)
    this.tooltipVisible = false

    this.editor.setOption('mode', 'text/x-core')
    this.editor.setOption('placeholder', '<Core elaboration failed...>')
    this.editor.on('cursorActivity', (doc) => this.markSelection(doc))

    this.editor.addOverlay({
      token: (stream) => {
        const rx_word = "\" "
        let ch = stream.peek()
        let word = ""

        if (rx_word.includes(ch) || ch === '\uE000' || ch === '\uE001') {
          stream.next()
          return null
        }

        while ((ch = stream.peek()) && !rx_word.includes(ch)){
          word += ch
          stream.next()
        }

        let re = /{-#.+[#,]/
        if (re.test(word))
          return "std"
      }
    }, { opaque: true, priority: 1000 }
    )

    this.editor.getWrapperElement().addEventListener('mousedown', (e) => {
      let edom = $(e.target);
      if (edom.hasClass('cm-std')) {
        if (edom.hasClass('tooltip')) {
          edom.removeClass('tooltip')
          edom.siblings('.tooltip-text').remove()
        } else {
          edom.addClass('tooltip')
          let content = getSTDSection(e.target.textContent)
          edom.after($('<span class="tooltip-text"></span>').append(content.data))
        }
      }
    })
  }

  getLocation(from, to) {
    let locations = ui.currentView.data.locs
    for (let i = 0; i < locations.length; i ++) {
      let loc = locations[i]
      if (loc.core.begin.line <= from.line && loc.core.end.line >= to.line)
        return loc
    }
    return null
  }

  mark(loc) {
    this.colorLines (loc.core.begin.line, loc.core.end.line, loc.color)
  }

  highlight() {
    let locations = ui.currentView.data.locs;
    for (let i = locations.length - 1; i >= 0; i--) {
      this.mark(locations[i])
    }
  }

  update() {
    this.setValue(ui.currentView.data.core)
  }

}

class TabAsm extends TabReadOnly {
  constructor(cc) {
    super(cc.name)

    this.editor.setOption('placeholder', '<Compilation failed...>')
    this.editor.setOption('mode', {name: "gas", architecture: "x86"})

    let toolbar   = $(document.createElement("div"))

    this.dropdownActive = $('<a href="#" class="dropbtn dropdown-toggle">'
                          + cc.name + '</a>')
    this.dropdown = $('<div class="dropdown"></div>')
    this.dropdown.append(this.dropdownActive)
    this.dropdown.append(this.createDropdownContent(this))

    this.options  = $('<input type="text" placeholder="Compiler options...">')

    toolbar.append(this.dropdown)
    toolbar.append(this.options)

    this.dom.content.addClass('tab-compiler')
    this.dom.content.prepend(toolbar)

    this.compile(cc)

    this.thanks = $(document.createElement("div"))

    let close = $(document.createElement("a"))
    close.attr("title", "Remove me!")
    close.addClass("remove-panel")
    close.text("✖")
    CodeMirror.on(close, "click", () => this.thanks.remove())

    let label = $(document.createElement("span"))
    label.text("I'm panel n°" + "blah")

    this.thanks.append(close)
    this.thanks.append(label)
    //this.editor.addPanel(this.thanks[0], {position: "bottom", stable: true});

    this.editor.on('cursorActivity', (doc) => this.markSelection(doc))

    this.cc = cc;
    this.lines = {}
    this.locations = {}
  }

  createDropdownContent()
  {
    let dropdown = $('<div class="dropdown-content"></div>')
    for (let i = 0; i < compilers.length; i++) {
      let cc  = compilers[i]
      let opt = $('<a href="#">' + cc.name + '</a>')
      opt.on('click', () => {
        this.compile(cc)
        this.dropdownActive.text(cc.name)
        this.setTitle(cc.name)
      })
      dropdown.append(opt)
    }
    return dropdown
  }

  update() {
    this.compile(this.cc)
  }

  updateLocations() {
    this.locations = {}
    let locs = ui.currentView.data.locs;
    for (let i = locs.length - 1; i >= 0; i--) {
      let l = locs[i].c.begin.line+1;
      if (this.locations[l] || !this.lines[l])
        continue;
      this.locations[l] = {
        begin: Math.min(...this.lines[l]),
        end: Math.max(...this.lines[l]),
        color: locs[i].color,
        source: locs[i]
      }
    }
  }


  getLocation(from, to) {
    for (const l in this.locations) {
      if (this.locations[l].begin <= from.line && this.locations[l].end >= to.line)
        return this.locations[l].source
    }
    return null
  }

  mark(loc) {
    let l = this.locations[loc.c.begin.line+1]
    if (l) this.colorLines (l.begin, l.end, l.color)
  }

  highlight() {
    let locs = ui.currentView.data.locs;
    for (let i = locs.length - 1; i >= 0; i--) {
      this.mark(locs[i])
    }
  }

  compile (cc) {
    ui.wait()
    $.ajax({
      headers: {Accept: 'application/json'},
      url: 'https://gcc.godbolt.org/api/compiler/'+cc.id+'/compile',
      type: 'POST',
      data: ui.currentView.getValue(),
      success: (data, status, query) => {
        console.log(data)
        let value = ''
        for (let i = 0; i < data.asm.length; i ++) {
          let asm = data.asm[i]
          value += asm.text + '\n'
          if (asm.source && asm.source.line) {
            if (!this.lines[asm.source.line])
              this.lines[asm.source.line] = []
            this.lines[asm.source.line].push(i)
          }
        }
        this.setValue(value)
        this.updateLocations()
        this.highlight()
        ui.done()
      }
    })
  }

}
