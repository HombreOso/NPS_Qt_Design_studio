/*
This is a UI file (.ui.qml) that is intended to be edited in Qt Design Studio only.
It is supposed to be strictly declarative and only uses a subset of QML. If you edit
this file manually, you might introduce QML code that is not supported by Qt Design Studio.
Check out https://doc.qt.io/qtcreator/creator-quick-ui-forms.html for details on .ui.qml files.
*/

import QtQuick
import QtQuick.Controls
import UntitledProject1

Rectangle {
    width: 900
    height: 800

    color: Constants.backgroundColor

    Text {
        text: qsTr("Hello UntitledProject1")
        anchors.centerIn: parent
        font.family: Constants.font.family
    }

    Slider {
        id: slider
        x: 18
        y: 662
        width: 512
        height: 40
        snapMode: RangeSlider.SnapOnRelease
        to: 100
        value: 0.5
    }

    Label {
        id: label
        x: 18
        y: 144
        width: 512
        height: 512
        text: qsTr("Label")
    }
}
